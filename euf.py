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
remove equivalent entries based on CBMC analysis
6. Walk the AST of all source files in the main project and return
all locations were functions from the change set are called
'''
import argparse, re, sys, os, traceback, multiprocessing, subprocess
from functools import partial
from pprint import pprint
from clang import cindex
from git.repo import Repo
from git.objects.commit import Commit

from cparser import CONFIG, DependencyFunction, DependencyFunctionChange, \
    ProjectInvocation, SourceDiff, SourceFile, BASE_DIR
from cparser.harness import create_harness, get_state_space, run_harness, add_includes_from_tu
from cparser.util import flatten, flatten_dict, mkdir_p, print_err, print_info, print_stage, rm_f, wait_on_cr
from cparser.change_set import add_rename_changes_based_on_blame, \
        get_changed_functions_from_diff, get_transative_changes_from_file, log_changed_functions
from cparser.impact_set import get_call_sites_from_file, log_impact_set, \
        pretty_print_impact_by_proj, pretty_print_impact_by_dep
from cparser.build import autogen_compile_db, build_goto_lib, create_worktree, \
        check_ccdb_fail
from cparser.enumerate_globals import write_rename_files

def filter_out_excluded(items: list, path_arr: list[str]) -> list:
    '''
    Filter out any files that are in excluded paths
    The paths are provided as python regex
    '''
    filtered = []

    for item,path in zip(items,path_arr):
        exclude = False

        for exclude_regex in CONFIG.EXCLUDE_REGEXES:
            try:
                if re.search(rf"{exclude_regex}", path):
                    exclude = True
                    break
            except re.error:
                print_err(f"Invalid regex provided: {exclude_regex}")
                traceback.print_exc()
                sys.exit(-1)

        if not exclude:
            filtered.append(item)

    return filtered

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

def run():
    mkdir_p(CONFIG.EUF_CACHE)
    mkdir_p(CONFIG.RESULTS_DIR)

    # Set the path to the clang library (platform dependent)
    if not os.path.exists(CONFIG.LIBCLANG):
        print_err(f"Missing path to libclang: {CONFIG.LIBCLANG}")
        sys.exit(1)
    else:
        cindex.Config.set_library_file(CONFIG.LIBCLANG)

    # - - - Dependency - - - #
    DEP_REPO = Repo(CONFIG.DEPENDENCY_DIR)
    try:
        _ = DEP_REPO.active_branch
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
        print(f"Unable to find old commit: {CONFIG.COMMIT_OLD}")
        sys.exit(-1)
    if not COMMIT_NEW:
        print(f"Unable to find new commit: {CONFIG.COMMIT_NEW}")
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

    NEW_DEP_REPO = Repo(DEPENDENCY_NEW)

    if not CONFIG.SKIP_BLAME:
        # Add additional diffs based on git-blame that were not recorded
        ADDED_DIFF = list(filter(lambda d: \
                    str(d.a_path).endswith(".c") and \
                    'A' == d.change_type,
            COMMIT_OLD.diff(COMMIT_NEW)
        ))

        add_rename_changes_based_on_blame(NEW_DEP_REPO, ADDED_DIFF, DEP_SOURCE_DIFFS)

    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Git Diff")
        print("\n".join([ f"a/{d.old_path} -> b/{d.new_path}" \
                for d in DEP_SOURCE_DIFFS ]) + "\n")
        wait_on_cr()

    if CONFIG.SHOW_DIFFS:
        for d in DEP_SOURCE_DIFFS:
            subprocess.run(["git", # Force pager for every file
                "-c", "core.pager=less -+F -c",
                "diff", "--no-index", "--color=always",
                f"{DEPENDENCY_OLD}/{d.old_path}",
                f"{DEPENDENCY_NEW}/{d.new_path}" ])
        sys.exit(0)

    DEP_SOURCE_DIFFS = filter_out_excluded(DEP_SOURCE_DIFFS, \
            [ d.old_path for d in DEP_SOURCE_DIFFS ] )

    # Update the project root in case the source code and .git
    # folder are not both at the root of the project
    dep_source_root = CONFIG.DEP_SOURCE_ROOT.removeprefix(CONFIG.DEPENDENCY_DIR) \
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
        print_err(f"Failed to parse {DEP_SOURCE_ROOT_OLD}/compile_commands.json")
        sys.exit(-1)
    try:
        DEP_DB_NEW: cindex.CompilationDatabase  = \
                cindex.CompilationDatabase.fromDirectory(DEP_SOURCE_ROOT_NEW)
    except cindex.CompilationDatabaseError as e:
        print_err(f"Failed to parse {DEP_SOURCE_ROOT_NEW}/compile_commands.json")
        sys.exit(-1)

    # Extract compile flags for each file that was changed
    for diff in DEP_SOURCE_DIFFS:
        diff.old_compile_args = get_compile_args(DEP_DB_OLD, diff.old_path)
        diff.new_compile_args = get_compile_args(DEP_DB_NEW, diff.new_path)

    # - - - Main project - - - #
    # Gather a list of all the source files in the main project
    main_repo = Repo(CONFIG.PROJECT_DIR)
    PROJECT_SOURCE_FILES = filter(lambda p: str(p).endswith(".c"),
        [ e.path for e in main_repo.tree().traverse() ] # type: ignore
    )

    try:
        MAIN_DB = cindex.CompilationDatabase.fromDirectory(CONFIG.PROJECT_DIR)
    except cindex.CompilationDatabaseError as e:
        check_ccdb_fail(CONFIG.PROJECT_DIR)
        sys.exit(-1)

    PROJECT_SOURCE_FILES = [ SourceFile(
        new_path = filepath, # type: ignore
        new_compile_args = get_compile_args(MAIN_DB, filepath) # type: ignore
    ) for filepath in PROJECT_SOURCE_FILES ]

    # - - - Change set - - - #
    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Change set")

    LOG_DIR = f"{CONFIG.RESULTS_DIR}/{CONFIG.DEPLIB_NAME.removesuffix('.a')}"+\
        f"_{COMMIT_OLD.hexsha[:4]}_{COMMIT_NEW.hexsha[:4]}"

    if CONFIG.ENABLE_RESULT_LOG:
        mkdir_p(LOG_DIR)

    CHANGED_FUNCTIONS: list[DependencyFunctionChange] = []
    TU_INCLUDES = {}

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
            CHANGED_FUNCTIONS = list(filter(lambda f: \
                    not f.old.ident.spelling in CONFIG.IGNORE_FUNCTIONS,
                CHANGED_FUNCTIONS[:]))

            if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
                pprint(CHANGED_FUNCTIONS)
    except Exception:
        traceback.print_exc()
        sys.exit(-1)

    wait_on_cr()
    log_changed_functions(CHANGED_FUNCTIONS, f"{LOG_DIR}/change_set.csv")

    # Create a list of all files from the dependency
    # used for transative call analysis and state space estimation
    DEP_SOURCE_FILES = filter(lambda p: str(p).endswith(".c"),
        [ e.path for e in NEW_DEP_REPO.tree().traverse() ] # type: ignore
    )

    DEP_SOURCE_FILES = [ SourceFile(
        new_path = filepath, # type: ignore
        new_compile_args = get_compile_args(DEP_DB_NEW, filepath) # type: ignore
    ) for filepath in DEP_SOURCE_FILES ]

    DEP_SOURCE_FILES = filter_out_excluded(DEP_SOURCE_FILES, \
            [ f.new_path for f in DEP_SOURCE_FILES  ])

    # - - - Reduction of change set - - - #
    if CONFIG.FULL:
        if CONFIG.VERBOSITY >= 1:
            print_stage("Reduction")

        write_rename_files(DEPENDENCY_OLD, DEP_DB_OLD)

        # Compile the old and new version of the dependency as a set of 
        # goto-bin files
        if (new_lib := build_goto_lib(DEP_SOURCE_ROOT_NEW, DEPENDENCY_NEW, False)) == "":
            sys.exit(-1)
        if (old_lib := build_goto_lib(DEP_SOURCE_ROOT_OLD, DEPENDENCY_OLD, True)) == "":
            sys.exit(-1)

        # Copy any required headers into the include
        # directory of the driver
        os.makedirs(CONFIG.OUTDIR, exist_ok=True)

        # Attempt to derive valid input parameters for each changed function based on invocations
        # in the old and new version of the dependency as well as the main project
        #for source_file in DEP_SOURCE_FILES:
        #    get_state_space(CHANGED_FUNCTIONS, DEP_SOURCE_ROOT_OLD, source_file)
        #exit(0)


        script_env = CONFIG.get_script_env()
        script_env.update({
            'NEW_LIB': new_lib,
            'OLD_LIB': old_lib,
            'OUTDIR': CONFIG.OUTDIR,
            'OUTFILE': CONFIG.CBMC_OUTFILE,
            'EUF_ENTRYPOINT': CONFIG.EUF_ENTRYPOINT,
            'CBMC_OPTS_STR': CONFIG.CBMC_OPTS_STR
        })

        log_file = f"{LOG_DIR}/cbmc.csv"
        rm_f(log_file)

        harness_dir = f"{DEP_SOURCE_ROOT_OLD}/{CONFIG.HARNESS_DIR}"
        mkdir_p(harness_dir)

        total = len(CHANGED_FUNCTIONS)

        # Retrieve a list of the headers that each TU uses
        # We will need to include these in the driver
        # for types etc. to be defined
        for diff in DEP_SOURCE_DIFFS:
            add_includes_from_tu(diff, DEPENDENCY_OLD, TU_INCLUDES)

        for i,change in enumerate(CHANGED_FUNCTIONS[:]):
            func_name = change.old.ident.spelling

            if CONFIG.ONLY_ANALYZE != "" and \
                    CONFIG.ONLY_ANALYZE != func_name:
                continue

            # - - - Harness generation - - - #
            # Begin by generating an identity driver and verify that it
            # passes as equivalent, then generate the actual driver and check if the
            # change is considered equivalent
            harness_path = f"{harness_dir}/{change.old.ident.spelling}{CONFIG.IDENTITY_HARNESS}.c"

            if CONFIG.USE_EXISTING_DRIVERS and os.path.exists(harness_path):
                pass # Use existing driver
            elif not create_harness(change, harness_path, \
                    TU_INCLUDES[change.old.filepath], identity=True):
                continue # Generation failed

            # Run the identity harness
            if run_harness(change, script_env, harness_path, func_name, \
                log_file, i+1, total, quiet = CONFIG.SILENT_IDENTITY_VERIFICATION):

                harness_path = f"{harness_dir}/{change.old.ident.spelling}.c"

                if CONFIG.USE_EXISTING_DRIVERS and os.path.exists(harness_path):
                    pass # Use existing driver
                elif not create_harness(change, harness_path, \
                        TU_INCLUDES[change.old.filepath], identity=False):
                    continue # Generation failed

                # Run the actual harness
                if run_harness(change, script_env, harness_path, func_name, log_file, \
                        i+1, total, quiet = CONFIG.SILENT_VERIFICATION):
                    # Remove the change from the change set if the equivalance check passes
                    CHANGED_FUNCTIONS.remove(change)

        log_changed_functions(CHANGED_FUNCTIONS, f"{LOG_DIR}/reduced_set.csv")
        print_info(f"Change set reduction: {total} -> {len(CHANGED_FUNCTIONS)}")

    if CONFIG.SKIP_IMPACT:  sys.exit(0)

    # - - - Transitive change set propagation - - - #
    # To include functions that have not had a textual change but call a 
    # function that has changed, we perform a configurable number of 
    # additional passes were we look for invocations of changed functions 
    # in the dependency 
    #
    # Note that we perform propagation after the reduction step
    # We do not want to use CBMC analysis for transitive function calls
    #
    # We only need to look through the files in the new version

    if CONFIG.VERBOSITY >= 1:
        print_stage("Transitive change set")
        wait_on_cr()
    TRANSATIVE_CHANGED_FUNCTIONS = {}
    os.chdir(DEPENDENCY_NEW)

    for _ in range(CONFIG.TRANSATIVE_PASSES):
        try:
            #for source_file in DEP_SOURCE_FILES:
            #    get_transative_changes_from_file(source_file,DEP_SOURCE_ROOT_NEW,CHANGED_FUNCTIONS)
            #exit(0)

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
                    if (idx := [ c.new for c in CHANGED_FUNCTIONS ].index(key)):
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
            sys.exit(-1)

    log_changed_functions(CHANGED_FUNCTIONS, f"{LOG_DIR}/trans_change_set.csv")

    if CONFIG.VERBOSITY >= 2:
        print_stage("Complete set")
        pprint(CHANGED_FUNCTIONS)


    # - - - Impact set - - - #
    if CONFIG.VERBOSITY >= 1:
        print_stage("Impact set")
        wait_on_cr()
    CALL_SITES: list[ProjectInvocation]      = []

    os.chdir(CONFIG.PROJECT_DIR)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations (the impact set)
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            CALL_SITES = flatten(p.map(
                partial(get_call_sites_from_file,
                    changed_functions = set(CHANGED_FUNCTIONS)
                ),
                PROJECT_SOURCE_FILES
            ))

            if CONFIG.VERBOSITY >= 2 or len(CALL_SITES) == 0:
                pprint(CALL_SITES)
            else:
                if CONFIG.REVERSE_MAPPING:
                    pretty_print_impact_by_dep(CALL_SITES)
                else:
                    pretty_print_impact_by_proj(CALL_SITES)
            if CONFIG.ENABLE_RESULT_LOG:
                log_impact_set(CALL_SITES, f"{LOG_DIR}/impact_set.csv")
    except Exception as e:
        traceback.print_exc()
        sys.exit(-1)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be generated for both the project and the dependency."
    )
    parser.add_argument("--config", metavar="json", type=str, required=True,
        default="", help="JSON file containing a custom Config object to use")
    parser.add_argument("--diff", action='store_true', default=False,
        help='Print the diff between the files in the change set and exit')

    args = parser.parse_args()
    CONFIG.update_from_file(args.config)
    CONFIG.SHOW_DIFFS = args.diff # Ignored if given in config file
    if CONFIG.VERBOSITY >= 2:
        pprint(CONFIG)

    run()

    sys.exit(0)

