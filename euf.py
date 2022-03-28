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
    ProjectInvocation, SourceDiff, SourceFile, BASE_DIR
from cparser.util import flatten, flatten_dict, print_err, print_info, print_stage, remove_prefix
from cparser.change_set import add_rename_changes_based_on_blame, \
        get_changed_functions_from_diff, get_transative_changes_from_file
from cparser.impact_set import get_call_sites_from_file, \
        pretty_print_impact_by_proj, pretty_print_impact_by_dep
from cparser.build import autogen_compile_db, build_goto_lib, create_worktree, \
        compile_db_fail_msg
from cparser.transform import add_suffix_to_globals, \
        has_euf_internal_stash


def restore_and_exit(code: int = 0):
    '''
    Should be called when exiting the program after a successful call to
    `add_suffix_to_globals`

    Stash the changes in any repository that does not already have an 
    internal stash and has uncommited modifications. Restore any changes
    to reposistories that already have a stash
    Keeping the '_old' suffixes around would require
    a manual reset to use EUF agian
    '''
    if not CONFIG.FULL:
        sys.exit(code)

    repo_names = next(os.walk(CONFIG.EUF_CACHE))[1]

    for repo_name in repo_names:
        repo = Repo(f"{CONFIG.EUF_CACHE}/{repo_name}")
        try:
            # If the repository has changes that include the string '_old' 
            # and there is no internal stash associated with it
            # create a new stash
            if has_euf_internal_stash(repo, repo_name) == "" and \
                re.search(rf"{CONFIG.SUFFIX}", repo.git.diff()) != None: # type: ignore
                    print_info(f"Stashing changes in {repo_name}")
                    repo.git.stash(# type: ignore
                            message = f"{CONFIG.CACHE_INTERNAL_STASH} {repo_name}",
                    )
            # Otherwise checkout all the changes (we can restore them from the 
            # existing stash if need to run the analysis again)
            else:
                if CONFIG.VERBOSITY >= 3:
                    print_info(f"Discarding changes in {repo_name}")
                repo.git.checkout(".") # type: ignore

        except GitCommandError:
            traceback.print_exc()
            sys.exit(-1)

    sys.exit(code)

def get_compile_args(compile_db: cindex.CompilationDatabase,
    filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file
    and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
    if ccmds:
        compile_args                    = list(ccmds[0].arguments)
        # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
        # and add the default linker paths
        return compile_args[1:-1]
    else:
        raise Exception(f"Failed to retrieve compilation instructions for {filepath}")

if __name__ == '__main__':
    config_passed = '--config' in sys.argv

    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be present for both the project and the dependency."
    )

    parser.add_argument("project", type=str, nargs='?' if config_passed else 1,
        help='Project to analyze')
    parser.add_argument("--commit-new", metavar="hash", required=not config_passed,
        help='Git hash of the new commit in the dependency')
    parser.add_argument("--commit-old", metavar="hash", required=not config_passed,
        help='Git hash of the old (current) commit in the dependency')
    parser.add_argument("--dependency", metavar="directory", required=not config_passed, help=
        'The dependency to upgrade, should be an up-to-date git repository with the most recent commit checked out')
    parser.add_argument("--libclang", metavar="filepath",
        default=CONFIG.LIBCLANG, help=f"Path to libclang (default {CONFIG.LIBCLANG})")
    parser.add_argument("--deplib-name", metavar="string", required=not config_passed,
            help=f"The name (e.g. 'libcrypto.a') of the dependency's library")

    parser.add_argument("--goto-build-script", metavar='file', default=CONFIG.GOTO_BUILD_SCRIPT, help=
        f"Custom build script for generating a goto-bin library, ran instead of ./scripts/mk_goto.sh")
    parser.add_argument("--ccdb-build-script", metavar='file', default="", help=
        f"Custom build script for generating compile_commands.json for the dependency, see ./scripts/ccdb* for examples")
    parser.add_argument("--rename-script", metavar="file", type=str,
        default="", help=f"Shell scripts for additional processing of source files during the renaming process")
    parser.add_argument("--rename-blacklist", metavar='file', default="", help=
        f"Newline seperated file of names that should not be renamed")
    parser.add_argument("--json", action='store_true', default=False,
        help='Print results as JSON')
    parser.add_argument("--force-recompile", action='store_true', default=False,
        help='Always recompile dependencies')
    parser.add_argument("--skip-blame", action='store_true', default=False,
        help='Skip blame correlation')
    parser.add_argument("--full", action='store_true', default=False,
        help='Run the full analysis with CBMC')
    parser.add_argument("--skip-impact", action='store_true', default=False,
        help='Skip the final impact assessment step')
    parser.add_argument("--reverse-mapping", action='store_true', default=False,
        help='Print the impact set as a mapping from dependency changes to project invocations')
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
    parser.add_argument("--config", metavar="json", type=str,
        default="", help=f"JSON file containing a custom Config object to use")

    args = parser.parse_args()

    if config_passed:
        DEP_ONLY_PATH_OLD   = ""
        DEP_ONLY_PATH_NEW   = ""
        PROJECT_ONLY_PATH   = ""

        CONFIG.update_from_file(args.config)
    else:
        if not args.project:
            print("Missing project argument")
            sys.exit(1)

        DEP_ONLY_PATH_OLD   = args.dep_only_old
        DEP_ONLY_PATH_NEW   = args.dep_only_new
        PROJECT_ONLY_PATH   = args.project_only

        CONFIG.PROJECT_DIR         = args.project[0]
        CONFIG.DEPENDENCY_DIR      = args.dependency
        CONFIG.DEP_SOURCE_ROOT     = args.dep_source_root
        CONFIG.DEPLIB_NAME         = args.deplib_name

        CONFIG.VERBOSITY            = args.verbose
        CONFIG.RENAME_BLACKLIST     = args.rename_blacklist
        CONFIG.LIBCLANG             = args.libclang
        CONFIG.FULL                 = args.full
        CONFIG.UNWIND               = args.unwind
        CONFIG.DRIVER               = args.driver
        CONFIG.FORCE_RECOMPILE      = args.force_recompile
        CONFIG.SKIP_IMPACT          = args.skip_impact
        CONFIG.SKIP_BLAME           = args.skip_blame

        if args.commit_new != "":
            CONFIG.COMMIT_NEW   = args.commit_new
        if args.commit_old != "":
            CONFIG.COMMIT_OLD   = args.commit_old

        if args.goto_build_script != "":
            CONFIG.GOTO_BUILD_SCRIPT = args.goto_build_script
        if args.ccdb_build_script != "":
            CONFIG.CCDB_BUILD_SCRIPT = args.ccdb_build_script
        if args.rename_script != "":
            CONFIG.RENAME_SCRIPT     = args.rename_script

    CONFIG.SETX                 = str(CONFIG.VERBOSITY >= 2).lower()

    if CONFIG.VERBOSITY >= 1:
        pprint(CONFIG)

    if not os.path.exists(CONFIG.EUF_CACHE):
        os.mkdir(CONFIG.EUF_CACHE)

    # Set the path to the clang library (platform dependent)
    if not os.path.exists(CONFIG.LIBCLANG):
        print_err(f"Missing path to libclang: {CONFIG.LIBCLANG}")
        sys.exit(1)
    else:
        cindex.Config.set_library_file(CONFIG.LIBCLANG)

    # - - - Dependency - - - #
    DEP_REPO = Repo(CONFIG.DEPENDENCY_DIR)
    try:
        HEAD_BRANCH = DEP_REPO.active_branch
    except TypeError as e:
        print_err(f"Unable to read current branch name for {CONFIG.DEPENDENCY_DIR}\n{e}")
        sys.exit(1)

    # Find the objects that correspond to the old and new commit
    COMMIT_OLD: Commit = None # type: ignore
    COMMIT_NEW: Commit = None # type: ignore

    for commit in DEP_REPO.iter_commits():
        if commit.hexsha.startswith(CONFIG.COMMIT_NEW):
            COMMIT_NEW: Commit = commit
        elif commit.hexsha.startswith(CONFIG.COMMIT_OLD):
            COMMIT_OLD: Commit = commit

    if not COMMIT_OLD:
        print(f"Unable to find old commit: {args.commit_old}")
        sys.exit(-1)
    if not COMMIT_NEW:
        print(f"Unable to find new commit: {args.commit_new}")
        sys.exit(-1)


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


    DEP_NAME = os.path.basename(CONFIG.DEPENDENCY_DIR)
    DEPENDENCY_NEW = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{COMMIT_NEW.hexsha[:8]}"
    DEPENDENCY_OLD = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{COMMIT_OLD.hexsha[:8]}"

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    if not create_worktree(DEPENDENCY_NEW, COMMIT_NEW, DEP_REPO): sys.exit(-1)
    if not create_worktree(DEPENDENCY_OLD, COMMIT_OLD, DEP_REPO): sys.exit(-1)

    OLD_DEP_REPO = Repo(DEPENDENCY_OLD)
    NEW_DEP_REPO = Repo(DEPENDENCY_NEW)

    if not CONFIG.SKIP_BLAME:
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
                for d in DEP_SOURCE_DIFFS ]) + "\n")

    # Update the project root in case the source code and .git
    # folder are not both at the root of the project
    dep_source_root = remove_prefix(CONFIG.DEP_SOURCE_ROOT, CONFIG.DEPENDENCY_DIR) \
        if CONFIG.DEP_SOURCE_ROOT != "" \
        else ""

    DEP_SOURCE_ROOT_OLD = DEPENDENCY_OLD + dep_source_root
    DEP_SOURCE_ROOT_NEW = DEPENDENCY_NEW + dep_source_root

    if CONFIG.CCDB_BUILD_SCRIPT != "":
        try:
            script_env = CONFIG.get_script_env()
            script_env.update({
                'DEP_SOURCE_ROOT_OLD': DEP_SOURCE_ROOT_OLD,
                'DEP_SOURCE_ROOT_NEW': DEP_SOURCE_ROOT_NEW,
            })
            print_info(f"Running custom compile_commands.json generator: {CONFIG.CCDB_BUILD_SCRIPT}")
            (subprocess.run([ CONFIG.CCDB_BUILD_SCRIPT ],
                stdout = sys.stderr, cwd = BASE_DIR, env = script_env
            )).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
            sys.exit(-1)
    else:
        # Attempt to create the compilation database automatically
        # if they do not already exist
        if not autogen_compile_db(DEP_SOURCE_ROOT_OLD): sys.exit(-1)
        if not autogen_compile_db(DEP_SOURCE_ROOT_NEW): sys.exit(-1)
        if not autogen_compile_db(CONFIG.PROJECT_DIR): sys.exit(-1)

    # For the AST dump to contain a resolved view of the symbols
    # we need to provide the correct compile commands
    try:
        DEP_DB_OLD: cindex.CompilationDatabase  = \
            cindex.CompilationDatabase.fromDirectory(DEP_SOURCE_ROOT_OLD)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEP_SOURCE_ROOT_OLD)
        sys.exit(-1)
    try:
        DEP_DB_NEW: cindex.CompilationDatabase  = \
                cindex.CompilationDatabase.fromDirectory(DEP_SOURCE_ROOT_NEW)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEP_SOURCE_ROOT_NEW)
        sys.exit(-1)

    # Extract compile flags for each file that was changed
    for diff in DEP_SOURCE_DIFFS:
        diff.old_compile_args = get_compile_args(DEP_DB_OLD, diff.old_path)
        diff.new_compile_args = get_compile_args(DEP_DB_NEW, diff.new_path)

    if DEP_ONLY_PATH_NEW != "":
        DEP_SOURCE_DIFFS = list(filter(lambda d:
            d.new_path == DEP_ONLY_PATH_NEW, DEP_SOURCE_DIFFS))

    # - - - Main project - - - #
    # Gather a list of all the source files in the main project
    main_repo = Repo(CONFIG.PROJECT_DIR)
    PROJECT_SOURCE_FILES = filter(lambda p: str(p).endswith(".c"),
        [ e.path for e in main_repo.tree().traverse() ] # type: ignore
    )

    try:
        MAIN_DB = cindex.CompilationDatabase.fromDirectory(CONFIG.PROJECT_DIR)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(CONFIG.PROJECT_DIR)
        sys.exit(-1)

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
        sys.exit(-1)

    # - - - Harness generation - - - #
    # Regardless of which back-end we use to check equivalance, 
    # we will need a minimal program that invokes both versions of the changed 
    # function and then performs an assertion on all affected outputs
    #
    # TODO
    #

    # - - - Reduction of change set - - - #
    if CONFIG.FULL:
        try:
            if CONFIG.VERBOSITY >= 1:
                print_stage("Reduction")

            if not add_suffix_to_globals(DEPENDENCY_OLD, DEP_DB_OLD, CONFIG.SUFFIX):
                sys.exit(-1)

            # Compile the old and new version of the dependency as a goto-bin
            if (new_lib := build_goto_lib(DEP_SOURCE_ROOT_NEW)) == "":
                restore_and_exit(-1)
            if (old_lib := build_goto_lib(DEP_SOURCE_ROOT_OLD)) == "":
                exit(-1) # restore_and_exit(-1)

            os.makedirs(f"{BASE_DIR}/{CONFIG.OUTDIR}", exist_ok=True)

            script_env = CONFIG.get_script_env()
            script_env.update({
                'NEW_LIB': new_lib,
                'OLD_LIB': old_lib,
                'OUTDIR': f"{BASE_DIR}/{CONFIG.OUTDIR}",
                'UNWIND': str(CONFIG.UNWIND)
            })

            for change in CHANGED_FUNCTIONS:
                # TODO: pair each change with its own dedicated driver
                # based on the function being tested
                if DEP_ONLY_PATH_OLD != "" and \
                   DEP_ONLY_PATH_OLD != change.old.filepath:
                    continue

                script_env.update({
                    'DRIVER': CONFIG.DRIVER
                })
                try:
                    print("\n")
                    print_info(f"Starting CBMC analysis for {change.old}")
                    (subprocess.run([ f"{BASE_DIR}/scripts/cbmc_driver.sh" ],
                    env = script_env, stdout = sys.stderr, cwd = BASE_DIR
                    )).check_returncode()
                except subprocess.CalledProcessError:
                    traceback.print_exc()
                    restore_and_exit(-1)
                break

            restore_and_exit(0) # tmp
        except KeyboardInterrupt:
            restore_and_exit(-1)

    if CONFIG.SKIP_IMPACT:  restore_and_exit(0)

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
                        changed_functions = CHANGED_FUNCTIONS,
                        dep_root_dir = DEP_SOURCE_ROOT_NEW
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
            restore_and_exit(-1)


    if CONFIG.VERBOSITY >= 2:
        print_stage("Complete set")
        pprint(CHANGED_FUNCTIONS)


    # - - - Impact set - - - #
    if CONFIG.VERBOSITY >= 1:
        print_stage("Impact set")
    CALL_SITES: list[ProjectInvocation]      = []

    os.chdir(CONFIG.PROJECT_DIR)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations (the impact set)
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            CALL_SITES = flatten(p.map(
                partial(get_call_sites_from_file,
                changed_functions = set(CHANGED_FUNCTIONS)),
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
        restore_and_exit(-1)


    restore_and_exit(0)
