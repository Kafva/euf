#!/usr/bin/env python3
'''
Approach:
1. Determine what source files in the dependency have been 
modified (M) or renamed (R) since the last commit based on git labeling 
2. Walk the AST of the old and new version of each modified file
3. Consider any functions with a difference in the AST composition as
the base change-set
4. Perform a configurable number of passes where we add functions that
are transativly changed, i.e. functions that call a function that 
has been changed
5. Analyze each of the objects in the base change-set and 
remove equivilent entries
6. Walk the AST of all source files in the main project and return
all locations were functions from the change set are called
'''
import argparse, re, sys, os, traceback, multiprocessing, subprocess
from functools import partial
from pprint import pprint
from clang import cindex
from git.exc import GitCommandError
from git.repo import Repo
from git.objects.commit import Commit

from cparser import CONFIG, DependencyFunction, DependencyFunctionChange, \
    ProjectInvocation, SourceDiff, SourceFile, get_compile_args, BASE_DIR
from cparser.util import flatten, flatten_dict, print_err, print_info, print_stage, remove_prefix
from cparser.change_set import add_rename_changes_based_on_blame, \
        get_changed_functions_from_diff, get_transative_changes_from_file
from cparser.impact_set import get_call_sites_from_file, \
        pretty_print_impact_by_proj, pretty_print_impact_by_dep
from cparser.build import autogen_compile_db, build_goto_lib, create_worktree, \
        compile_db_fail_msg
from cparser.transform import add_suffix_to_globals, get_all_top_level_decls, \
        top_stash_is_euf_internal


def done(code: int = 0):
    '''
    Stash the changes in any repository that does not already have an 
    internal stash and has uncommited modifications
    Keeping the '_old' suffixes around would require
    a manual reset to use EUF agian
    '''
    repo_paths = next(os.walk(CONFIG.EUF_CACHE))[1]

    for repo_path in repo_paths:
        repo = Repo(f"{CONFIG.EUF_CACHE}/{repo_path}")
        try:
            if not top_stash_is_euf_internal(repo) and repo.git.diff() != "": # type: ignore
                print_info(f"Stashing changes in {repo_path}")
                repo.git.stash(message = CONFIG.CACHE_INTERNAL_STASH) # type: ignore
        except GitCommandError:
            traceback.print_exc()
            sys.exit(-1)

    sys.exit(code)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be present for both the project and the dependency."
    )

    parser.add_argument("project", type=str, nargs=1,
        help='Project to analyze')
    parser.add_argument("--commit-new", metavar="hash", required=True,
        help='Git hash of the new commit in the dependency')
    parser.add_argument("--commit-old", metavar="hash", required=True,
        help='Git hash of the old (current) commit in the dependency')
    parser.add_argument("--dependency", metavar="directory", required=True, help=
        'The dependency to upgrade, should be an up-to-date git repository with the most recent commit checked out')
    parser.add_argument("--libclang", metavar="filepath",
        default=CONFIG.LIBCLANG, help=f"Path to libclang (default {CONFIG.LIBCLANG})")

    parser.add_argument("--json", action='store_true', default=False,
        help='Print results as JSON')
    parser.add_argument("--force-recompile", action='store_true', default=False,
        help='Always recompile dependencies')
    parser.add_argument("--full", action='store_true', default=False,
        help='Run the full analysis with CBMC')
    parser.add_argument("--reverse-mapping", action='store_true', default=False,
        help='Print the impact set as a mapping from dependency changes to project invocations')
    parser.add_argument("--dump-top-level-decls", action='store_true', default=False,
        help='Dump the names of ALL top level declarations in the old version of the dependency')
    parser.add_argument("--verbose", metavar='level', type=int,
        default=CONFIG.VERBOSITY,
        help=f"Verbosity level in output, 0-3, (default 0)")
    parser.add_argument("--unwind", metavar='count', default=CONFIG.UNWIND, help=
        f"Unwindings to perform for loops during CBMC analysis")
    parser.add_argument("--nprocs", metavar='count', default=CONFIG.NPROC, help=
        f"The number of processes to spawn for parallel execution (default {CONFIG.NPROC})")
    parser.add_argument("--dep-only-new", metavar="filepath", default="", help=
        'Only process a specific path of the dependency (uses the path in the new commit)')
    parser.add_argument("--dep-only-old", metavar="filepath", default="", help=
        'Only process a specific path of the dependency (uses the path in the old commit)')
    parser.add_argument("--driver", metavar="filepath", default="", help=
        'The entrypoint to use for CBMC tests')
    parser.add_argument("--project-only", metavar="filepath", default="", help=
        'Only process a specific path of the main project')
    parser.add_argument("--dep-source-root", metavar="filepath",
        default="", help=f"Path to source root with ./configure script (same as git root by default)")
    parser.add_argument("--exclude-dirs", metavar="directories", type=str,
        default="", help=f"Comma separated string of directory paths relative to the old root of the dependency that should be excluded from analysis")

    args = parser.parse_args()

    if args.commit_new == "" or args.commit_old == "" or \
        args.dependency == "" or len(args.project) == 0:
        print("Missing required option/argument")
        sys.exit(1)

    CONFIG.VERBOSITY    = args.verbose
    PROJECT_DIR         = os.path.abspath(args.project[0])
    DEPENDENCY_DIR      = os.path.abspath(args.dependency)
    DEP_ONLY_PATH_OLD   = args.dep_only_old
    DEP_ONLY_PATH_NEW   = args.dep_only_new
    PROJECT_ONLY_PATH   = args.project_only
    CONFIG.LIBCLANG     = args.libclang

    # Set the path to the clang library (platform dependent)
    if not os.path.exists(CONFIG.LIBCLANG):
        print_err(f"Missing path to libclang: {CONFIG.LIBCLANG}")
        sys.exit(1)
    else:
        cindex.Config.set_library_file(CONFIG.LIBCLANG)

    # - - - Dependency - - - #
    DEP_REPO = Repo(DEPENDENCY_DIR)
    try:
        HEAD_BRANCH = DEP_REPO.active_branch
    except TypeError as e:
        print_err(f"Unable to read current branch name for {DEPENDENCY_DIR}\n{e}")
        sys.exit(1)

    # Find the objects that correspond to the old and new commit
    COMMIT_OLD: Commit = None # type: ignore
    COMMIT_NEW: Commit = None # type: ignore

    for commit in DEP_REPO.iter_commits():
        if commit.hexsha == args.commit_new:
            COMMIT_NEW: Commit = commit
        elif commit.hexsha == args.commit_old:
            COMMIT_OLD: Commit = commit

    if not COMMIT_OLD:
        print(f"Unable to find old commit: {args.commit_old}")
        sys.exit(1)
    if not COMMIT_NEW:
        print(f"Unable to find new commit: {args.commit_new}")
        sys.exit(1)


    # Only include modified (M) and renamed (R) '.c' files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation:
    #   e.g. `foo.c -> src/foo.c`
    COMMIT_DIFF = filter(lambda d: \
                str(d.a_path).endswith(".c") and \
                re.match("M|R", d.change_type),
        COMMIT_OLD.diff(COMMIT_NEW)
    )

    DEP_SOURCE_DIFFS = [ SourceDiff(
                new_path = d.b_path,
                old_path = d.a_path,
                new_compile_args = [],
                old_compile_args = []
    ) for d in COMMIT_DIFF ]


    DEP_NAME = os.path.basename(DEPENDENCY_DIR)
    DEPENDENCY_NEW = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{COMMIT_NEW.hexsha[:8]}"
    DEPENDENCY_OLD = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{COMMIT_OLD.hexsha[:8]}"

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    if not create_worktree(DEPENDENCY_NEW, DEPENDENCY_DIR, COMMIT_NEW): done(-1)
    if not create_worktree(DEPENDENCY_OLD, DEPENDENCY_DIR, COMMIT_OLD): done(-1)

    OLD_DEP_REPO = Repo(DEPENDENCY_OLD)
    NEW_DEP_REPO = Repo(DEPENDENCY_NEW)

    # Add additional diffs based on git-blame that were not recorded
    ADDED_DIFF = list(filter(lambda d: \
                str(d.a_path).endswith(".c") and \
                'A' == d.change_type,
        COMMIT_OLD.diff(COMMIT_NEW)
    ))

    add_rename_changes_based_on_blame(NEW_DEP_REPO, ADDED_DIFF, DEP_SOURCE_DIFFS)

    # Filter out any files that are under excluded directories
    if args.exclude_dirs != "":
        for exclude_dir in args.exclude_dirs.split(","):

            DEP_SOURCE_DIFFS = list(filter(lambda d:
                    not os.path.dirname(d.old_path).endswith(
                        remove_prefix(exclude_dir, "./")
                    ),
                    DEP_SOURCE_DIFFS
            ))

    if CONFIG.VERBOSITY >= 1:
        print_stage("Git Diff")
        print("\n".join([ f"a/{d.old_path} -> b/{d.new_path}" \
                for d in DEP_SOURCE_DIFFS ]))

    # Update the project root in case the source code and .git
    # folder are not both at the root of the project
    DEP_SOURCE_ROOT = os.path.abspath(args.dep_source_root)

    dep_source_root = remove_prefix(DEP_SOURCE_ROOT, DEPENDENCY_DIR) \
        if args.dep_source_root != "" \
        else ""

    DEP_SOURCE_ROOT_OLD = DEPENDENCY_OLD + dep_source_root
    DEP_SOURCE_ROOT_NEW = DEPENDENCY_NEW + dep_source_root

    # Attempt to create the compiliation database automatically
    # if they do not already exist
    if not autogen_compile_db(DEP_SOURCE_ROOT_OLD): done(-1)
    if not autogen_compile_db(DEP_SOURCE_ROOT_NEW): done(-1)
    if not autogen_compile_db(PROJECT_DIR): done(-1)

    # For the AST dump to contain a resolved view of the symbols
    # we need to provide the correct compile commands
    try:
        DEP_DB_OLD: cindex.CompilationDatabase  = \
            cindex.CompilationDatabase.fromDirectory(DEP_SOURCE_ROOT_OLD)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEP_SOURCE_ROOT_OLD)
        done(-1)
    try:
        DEP_DB_NEW: cindex.CompilationDatabase  = \
                cindex.CompilationDatabase.fromDirectory(DEP_SOURCE_ROOT_NEW)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEP_SOURCE_ROOT_NEW)
        done(-1)

    # Extract compile flags for each file that was changed
    for diff in DEP_SOURCE_DIFFS:
        diff.old_compile_args = get_compile_args(DEP_DB_OLD, diff.old_path)
        diff.new_compile_args = get_compile_args(DEP_DB_NEW, diff.new_path)

    if DEP_ONLY_PATH_NEW != "":
        DEP_SOURCE_DIFFS = list(filter(lambda d:
            d.new_path == DEP_ONLY_PATH_NEW, DEP_SOURCE_DIFFS))

    # - - - (Debugging) Dump all top level symbols - - - #
    if args.dump_top_level_decls:
        decls =  get_all_top_level_decls(DEPENDENCY_OLD, DEP_DB_OLD)
        if not decls:
            done(-1)
        else:
            print('\n'.join(decls))
            done(0)

    # - - - Main project - - - #
    # Gather a list of all the source files in the main project
    main_repo = Repo(PROJECT_DIR)
    PROJECT_SOURCE_FILES = filter(lambda p: str(p).endswith(".c"),
        [ e.path for e in main_repo.tree().traverse() ] # type: ignore
    )

    try:
        MAIN_DB = cindex.CompilationDatabase.fromDirectory(PROJECT_DIR)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(PROJECT_DIR)
        done(-1)

    PROJECT_SOURCE_FILES = [ SourceFile(
        new_path = filepath, # type: ignore
        new_compile_args = get_compile_args(MAIN_DB, filepath) # type: ignore
    ) for filepath in PROJECT_SOURCE_FILES ]

    if PROJECT_ONLY_PATH != "":
        PROJECT_SOURCE_FILES = list(filter(lambda f:
            f.new_path == PROJECT_ONLY_PATH, PROJECT_SOURCE_FILES))

    # - - - Change set - - - #
    if CONFIG.VERBOSITY >= 2:
        print_stage("Change set")

    CHANGED_FUNCTIONS: list[DependencyFunctionChange] = []

    # Look through the old and new version of each delta
    # using NPROC parallel processes and save
    # the changed functions to `CHANGED_FUNCTIONS`
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            CHANGED_FUNCTIONS       = flatten(p.map(
                partial(get_changed_functions_from_diff,
                    old_root_dir=DEPENDENCY_OLD,
                    new_root_dir=DEPENDENCY_NEW
                ),
                DEP_SOURCE_DIFFS
            ))

            if CONFIG.VERBOSITY >= 1:
                pprint(CHANGED_FUNCTIONS)
    except Exception:
        traceback.print_exc()
        done(-1)


    done(0)
    # - - - Harness generation - - - #
    # Regardless of which back-end we use to check equivalance, 
    # we will need a minimal program that invokes both versions of the changed 
    # function and then performs an assertion on all affected outputs
    #
    # TODO
    #


    # - - - Reduction of change set - - - #
    if len(CHANGED_FUNCTIONS) > 0 and args.full and os.path.exists(args.driver):
        try:
            if CONFIG.VERBOSITY >= 1:
                print_stage("Reduction")

            if not add_suffix_to_globals(DEPENDENCY_OLD, DEP_DB_OLD, "_old"):
                done(-1)

            # Compile the old and new version of the dependency as a goto-bin
            if (new_lib := build_goto_lib(DEPENDENCY_NEW, args.force_recompile)) == "": done(-1)
            if (old_lib := build_goto_lib(DEPENDENCY_OLD, args.force_recompile)) == "": done(-1)

            os.makedirs(f"{BASE_DIR}/{CONFIG.OUTDIR}", exist_ok=True)

            script_env = os.environ.copy()
            script_env.update({
                'DEPENDENCY_NEW': DEPENDENCY_NEW,
                'DEPENDENCY_OLD': DEPENDENCY_OLD,
                'NEW_LIB': new_lib,
                'OLD_LIB': old_lib,
                'OUTDIR': f"{BASE_DIR}/{CONFIG.OUTDIR}",
                'UNWIND': str(args.unwind),
                'SETX': str(CONFIG.VERBOSITY >= 2).lower()
            })

            for change in CHANGED_FUNCTIONS:
                # TODO: pair each change with its own dedicated driver
                # based on the function being tested
                if DEP_ONLY_PATH_OLD != "" and \
                   DEP_ONLY_PATH_OLD != change.old.filepath:
                    continue

                script_env.update({
                    'DRIVER': args.driver
                })
                try:
                    print_info(f"Starting CBMC analysis for {change.old}")
                    (subprocess.run([ f"{BASE_DIR}/scripts/cbmc_driver.sh" ],
                    env = script_env, stdout = sys.stderr, cwd = BASE_DIR
                    )).check_returncode()
                except subprocess.CalledProcessError:
                    traceback.print_exc()
                    done(-1)
                break

            done(0) # tmp
        except KeyboardInterrupt:
            done(-1)


    # - - - Transitive change set propagation - - - #
    # To include functions that have not had a textual change but call a 
    # function that has changed, we perform a configurable number of 
    # additional passes were we look for invocations of changed functions 
    # in the dependency 
    #
    # Note that we perform propogation after the reduction step
    # We do not want to use CBMC analysis for transative function calls
    #
    # We only need to look through the files in the new version
    DEP_SOURCE_FILES = filter(lambda p: str(p).endswith(".c"),
        [ e.path for e in NEW_DEP_REPO.tree().traverse() ] # type: ignore
    )

    DEP_SOURCE_FILES = [ SourceFile(
        new_path = filepath, # type: ignore
        new_compile_args = get_compile_args(DEP_DB_NEW, filepath) # type: ignore
    ) for filepath in DEP_SOURCE_FILES ]

    if DEP_ONLY_PATH_NEW != "":
        DEP_SOURCE_FILES = list(filter(lambda f:
            f.new_path == DEP_ONLY_PATH_NEW, DEP_SOURCE_FILES))

    if CONFIG.VERBOSITY >= 1:
        print_stage("Transitive change set")
    TRANSATIVE_CHANGED_FUNCTIONS = {}
    os.chdir(DEPENDENCY_NEW)

    for _ in range(CONFIG.TRANSATIVE_PASSES):
        try:
            with multiprocessing.Pool(CONFIG.NPROC) as p:
                TRANSATIVE_CHANGED_FUNCTIONS       = flatten_dict(p.map(
                    partial(get_transative_changes_from_file,
                        changed_functions = CHANGED_FUNCTIONS
                    ),
                    DEP_SOURCE_FILES
                ))

            if CONFIG.VERBOSITY >= 1:
                pprint(TRANSATIVE_CHANGED_FUNCTIONS)

            for key,calls in TRANSATIVE_CHANGED_FUNCTIONS.items():
                try:
                    # Add calls to a function that already has been identified as changed
                    if (idx := list(map(lambda cfn: cfn.new,  CHANGED_FUNCTIONS)).index(key)):
                        CHANGED_FUNCTIONS[idx].invokes_changed_functions.extend(calls)
                except ValueError:
                    # Add a new function (with an indirect change) to the changed set
                    changed_function = DependencyFunctionChange(
                            old = DependencyFunction.empty(),
                            new = key,
                            invokes_changed_functions = calls,
                            direct_change = False
                    )
                    CHANGED_FUNCTIONS.append(changed_function)

        except Exception as e:
            traceback.print_exc()
            done(-1)

    if CONFIG.VERBOSITY >= 2:
        print_stage("Complete set")
        pprint(CHANGED_FUNCTIONS)

    # - - - Impact set - - - #
    if CONFIG.VERBOSITY >= 1:
        print_stage("Impact set")
    CALL_SITES: list[ProjectInvocation]      = []

    os.chdir(PROJECT_DIR)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations (the impact set)
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            CALL_SITES = flatten(p.map(
                partial(get_call_sites_from_file,
                changed_functions=CHANGED_FUNCTIONS),
                PROJECT_SOURCE_FILES
            ))

            if args.json:
                print("TODO")
            elif CONFIG.VERBOSITY >= 2:
                pprint(CALL_SITES)
            else:
                if args.reverse_mapping:
                    pretty_print_impact_by_dep(CALL_SITES)
                else:
                    pretty_print_impact_by_proj(CALL_SITES)
    except Exception as e:
        traceback.print_exc()
        done(-1)


    done(0)
