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
5. Inspect all calls in the dependency to the changed functions and
save 'state sets' for each parameter. The state set will contain all
constant values that the given parameter can be assigned during program
execution or be set as empty if the parameter recieves nondet() assignemnts
5. Analyze each of the objects in the base change-set and 
remove equivalent entries based on CBMC analysis
6. Walk the AST of all source files in the main project and return
all locations were functions from the change set are called
'''
import argparse, sys, os, traceback, multiprocessing, subprocess
from functools import partial
from pprint import pprint
from clang import cindex
from git.repo import Repo

from cparser import BASE_DIR
from cparser.config import CONFIG
from cparser.types import DependencyFunction, DependencyFunctionChange, FunctionState, \
    ProjectInvocation, SourceDiff, SourceFile
from cparser.arg_states import call_arg_states_plugin, \
        get_subdir_tus, join_arg_states_result
from cparser.harness import valid_preconds, create_harness, \
        get_I_flags_from_tu, run_harness, add_includes_from_tu
from cparser.util import flatten, flatten_dict, has_allowed_suffix, mkdir_p, print_info, \
        print_stage, remove_files_in, rm_f, time_end, time_start, wait_on_cr, print_err
from cparser.change_set import add_rename_changes_based_on_blame, \
        get_changed_functions_from_diff, get_transative_changes_from_file, log_changed_functions
from cparser.impact_set import get_call_sites_from_file, log_impact_set, \
        pretty_print_impact_by_proj, pretty_print_impact_by_dep
from cparser.build import build_goto_lib, create_ccdb
from cparser.enumerate_globals import write_rename_files
from cparser.scm import filter_out_excluded, get_commits, get_source_diffs, create_worktree

def state_space_analysis(symbols: list[str], target_source_dir: str, target_dir: str):
    target_name = os.path.basename(target_dir)

    start = time_start(f"Inspecting call sites ({target_name})...")
    outdir = f"{CONFIG.ARG_STATES_OUTDIR}/{target_name}"
    mkdir_p(outdir)
    remove_files_in(outdir)
    subdir_tus = get_subdir_tus(target_source_dir, target_dir)
    if CONFIG.VERBOSITY >= 3:
        print("Subdirectories to analyze: ", end='')
        print([ p.removeprefix(f"{target_source_dir}/") for p in subdir_tus.keys()])

    with multiprocessing.Pool(CONFIG.NPROC) as p:
        for subdir, subdir_tu in subdir_tus.items():
            # Run parallel processes for different symbols
            p.map(partial(call_arg_states_plugin,
                outdir = outdir,
                target_dir = target_source_dir,
                subdir = subdir,
                subdir_tu = subdir_tu,
                quiet = True),
                symbols
            )

    time_end(f"State space analysis ({target_name})", start)

def impact_stage(log_dir:str, project_source_files: list[SourceFile],
 changed_functions: list[DependencyFunctionChange]):
    ''' - - - Impact set - - - '''
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
                    changed_functions = set(changed_functions)
                ),
                project_source_files
            ))

            if CONFIG.VERBOSITY >= 2 or len(CALL_SITES) == 0:
                pprint(CALL_SITES)
            else:
                if CONFIG.REVERSE_MAPPING:
                    pretty_print_impact_by_dep(CALL_SITES)
                else:
                    pretty_print_impact_by_proj(CALL_SITES)
            if CONFIG.ENABLE_RESULT_LOG:
                log_impact_set(CALL_SITES, f"{log_dir}/impact_set.csv")
    except Exception:
        traceback.print_exc()
        sys.exit(-1)

def get_source_files(path: str, ccdb: cindex.CompilationDatabase) -> list[SourceFile]:
    repo = Repo(path)
    source_files = filter(lambda p: has_allowed_suffix(p),
        [ e.path for e in repo.tree().traverse() ] # type: ignore
    )

    source_files = []
    for e in repo.tree().traverse(): # type: ignore
        if has_allowed_suffix(e.path):
            source_files.append(
                SourceFile.new(e.path,ccdb,path)
            )

    return source_files

def ast_diff_stage(dep_old:str, dep_new:str,
 dep_source_diffs: list[SourceDiff]) -> list[DependencyFunctionChange]:
    '''
    Look through the old and new version of each delta
    using NPROC parallel processes and save
    the changed functions to `changed_functions`
    '''
    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Change set")

    changed_functions = []
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            changed_functions       = flatten(p.map(
                partial(get_changed_functions_from_diff,
                    old_root_dir=dep_old,
                    new_root_dir=dep_new
                ),
                dep_source_diffs
            ))
            changed_functions = list(filter(lambda f: \
                    not f.old.ident.spelling in CONFIG.IGNORE_FUNCTIONS,
                changed_functions[:]))

            if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "" and not CONFIG.SHOW_DIFFS:
                pprint(changed_functions)
    except Exception:
        traceback.print_exc()
        sys.exit(-1)

    os.chdir(BASE_DIR) # cwd changes during compilation

    if CONFIG.SHOW_DIFFS:
        for c in changed_functions:
            print(c.divergence())
        wait_on_cr(always=True)

        for d in dep_source_diffs:
            cmd = ["git", # Force pager for every file
                "-c", "core.pager=less -+F -c",
                "diff", "--no-index", "--color=always",
                "--function-context",
                f"{dep_old}/{d.old_path}",
                f"{dep_new}/{d.new_path}" ]
            print(' '.join(cmd))
            subprocess.run(cmd)

        sys.exit(0)

    return changed_functions

def git_diff_stage(dep_repo: Repo, dep_new: str, dep_old: str,
 dep_db_old: cindex.CompilationDatabase, dep_db_new: cindex.CompilationDatabase
 ) -> list[SourceDiff]:
    ''' Find the objects that correspond to the old and new commit '''
    (commit_old, commit_new) = get_commits(dep_repo)

    # Only include modified (M) and renamed (R) '.c' files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation:
    #   e.g. `foo.c -> src/foo.c`
    dep_source_diffs = get_source_diffs(commit_old, commit_new)

    dep_source_diffs = filter_out_excluded(dep_source_diffs, \
            [ d.old_path for d in dep_source_diffs ] )

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    if not create_worktree(dep_new, CONFIG.COMMIT_NEW, dep_repo): sys.exit(-1)
    if not create_worktree(dep_old, CONFIG.COMMIT_OLD, dep_repo): sys.exit(-1)

    if not CONFIG.SKIP_BLAME:
        # Add additional diffs based on git-blame that were not recorded
        added_diff = list(filter(lambda d: \
                    has_allowed_suffix(d.a_path) and
                    'A' == d.change_type,
                commit_old.diff(commit_new) # type: ignore
        ))

        add_rename_changes_based_on_blame(
                Repo(dep_new), added_diff, dep_source_diffs
        )

    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Git Diff")
        print("\n".join([ f"a/{d.old_path} -> b/{d.new_path}" \
                for d in dep_source_diffs ]) + "\n")
        wait_on_cr()

    # Extract compile flags for each file that was changed
    for diff in dep_source_diffs:
        (diff.old_compile_dir, diff.old_compile_args) = \
                SourceFile.get_compile_args(dep_db_old, diff.old_path, dep_old)
        (diff.new_compile_dir, diff.new_compile_args) = \
                SourceFile.get_compile_args(dep_db_new, diff.new_path, dep_new)

    return dep_source_diffs

def run():
    ''' - - - Setup - - - '''
    # Set the path to the clang library (platform dependent)
    if not os.path.exists(CONFIG.LIBCLANG):
        if not os.path.exists(CONFIG.FALLBACK_LIBCLANG):
            print_err(f"Missing path to libclang: {CONFIG.LIBCLANG}")
            sys.exit(1)
        else:
            CONFIG.LIBCLANG = CONFIG.FALLBACK_LIBCLANG

    cindex.Config.set_library_file(CONFIG.LIBCLANG)

    DEP_REPO = Repo(CONFIG.DEPENDENCY_DIR)
    DEP_NAME = os.path.basename(CONFIG.DEPENDENCY_DIR)

    LOG_DIR = f"{CONFIG.RESULTS_DIR}/{CONFIG.DEPLIB_NAME.removesuffix('.a')}"+\
        f"_{CONFIG.COMMIT_OLD[:4]}_{CONFIG.COMMIT_NEW[:4]}"

    # Dependency .git directories
    dep_new = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{CONFIG.COMMIT_NEW[:8]}"
    dep_old = f"{CONFIG.EUF_CACHE}/{DEP_NAME}-{CONFIG.COMMIT_OLD[:8]}"

    # Source code directory (usually same as .git directory)
    dep_source_root = CONFIG.DEP_SOURCE_ROOT.removeprefix(CONFIG.DEPENDENCY_DIR) \
        if CONFIG.DEP_SOURCE_ROOT != "" \
        else ""

    dep_source_root_old = dep_old + dep_source_root
    dep_source_root_new = dep_new + dep_source_root

    if CONFIG.ENABLE_RESULT_LOG:
        mkdir_p(LOG_DIR)

    mkdir_p(CONFIG.EUF_CACHE)
    mkdir_p(CONFIG.RESULTS_DIR)
    mkdir_p(CONFIG.ARG_STATES_OUTDIR)

    try:
        _ = DEP_REPO.active_branch
    except TypeError as e:
        print_err(f"Unable to read current branch name for {CONFIG.DEPENDENCY_DIR}\n{e}")
        sys.exit(1)

    # Attempt to create the compilation database automatically
    # if they do not already exist
    dep_db_new = create_ccdb(dep_source_root_new)
    dep_db_old = create_ccdb(dep_source_root_old)
    main_db = create_ccdb(CONFIG.PROJECT_DIR)

    # Gather a list of all the source files in the main project
    PROJECT_SOURCE_FILES = get_source_files(CONFIG.PROJECT_DIR, main_db)

    # Create a list of all files from the dependency
    # used for transative call analysis and state space estimation
    DEP_SOURCE_FILES = get_source_files(dep_old, dep_db_old)

    # - - - Git diff - - - #
    dep_source_diffs = git_diff_stage(DEP_REPO,
        dep_old, dep_new, dep_db_old, dep_db_new
    )

    # - - - Change set - - - #
    CHANGED_FUNCTIONS = ast_diff_stage(dep_old, dep_new, dep_source_diffs)
    TU_INCLUDES = {}

    wait_on_cr()
    log_changed_functions(CHANGED_FUNCTIONS, f"{LOG_DIR}/change_set.csv")

    # - - - Reduction of change set - - - #
    if CONFIG.FULL:
        if CONFIG.VERBOSITY >= 1:
            print_stage("Reduction")

        write_rename_files(dep_old, dep_db_old)

        # Compile the old and new version of the dependency as a set of 
        # goto-bin files
        if (new_lib := build_goto_lib(dep_source_root_new, dep_new, False)) == "":
            sys.exit(-1)
        if (old_lib := build_goto_lib(dep_source_root_old, dep_old, True)) == "":
            sys.exit(-1)

        # Copy any required headers into the include
        # directory of the driver
        os.makedirs(CONFIG.OUTDIR, exist_ok=True)

        # - - - State space - - - #
        # Derive valid input parameters for each changed function based on invocations
        # in the old and new version of the dependency as well as the main project
        # This process is performed using an external clang plugin
        #
        # FIXME: If the main project has an internal function with the same name as a function
        # in the change set these will not be differentiated and likely cause params
        # to be set as nondet when they could potentially be det.
        remove_files_in(CONFIG.ARG_STATES_OUTDIR)

        log_file = f"{LOG_DIR}/reduce.csv"
        rm_f(log_file)

        # Retrieve a list of the headers that each TU uses
        # We will need to include these in the driver
        # for types etc. to be defined
        IFLAGS = get_I_flags_from_tu(dep_source_diffs, dep_old, dep_source_root_old)

        # Exclude functions that we are not going to analyze
        changes_to_analyze = []
        for c in CHANGED_FUNCTIONS:
            if valid_preconds(c,IFLAGS,logfile="",quiet=True):
                changes_to_analyze.append(c.old.ident.spelling)

        state_space_analysis(changes_to_analyze, dep_source_root_old, dep_old)
        #state_space_analysis(changes_to_analyze, dep_source_root_new, dep_new)
        #state_space_analysis(changes_to_analyze, CONFIG.PROJECT_DIR, CONFIG.PROJECT_DIR) TODO: takes to long

        # Join the results from each analysis
        old_name    = os.path.basename(dep_old)
        new_name    = os.path.basename(dep_new)
        proj_name   = os.path.basename(CONFIG.PROJECT_DIR)
        ARG_STATES  = join_arg_states_result([ old_name, new_name, proj_name ])

        script_env = CONFIG.get_script_env()
        script_env.update({
            'NEW_LIB': new_lib,
            'OLD_LIB': old_lib,
            'OUTDIR': CONFIG.OUTDIR,
            'OUTFILE': CONFIG.CBMC_OUTFILE,
            'EUF_ENTRYPOINT': CONFIG.EUF_ENTRYPOINT,
            'CBMC_OPTS_STR': CONFIG.CBMC_OPTS_STR
        })

        harness_dir = f"{dep_source_root_old}/{CONFIG.HARNESS_DIR}"
        mkdir_p(harness_dir)

        total = len(CHANGED_FUNCTIONS)

        for diff in dep_source_diffs:
            add_includes_from_tu(diff, dep_old, dep_source_root_old, IFLAGS, TU_INCLUDES)

        for i,change in enumerate(CHANGED_FUNCTIONS[:]):
            # - - - Harness generation - - - #
            # Begin by generating an identity driver and verify that it
            # passes as equivalent, then generate the actual driver and check if the
            # change is considered equivalent
            func_name = change.old.ident.spelling

            if CONFIG.ONLY_ANALYZE != "" and \
               CONFIG.ONLY_ANALYZE != func_name:
                continue

            # Log the reason for why a change could not be verified
            if not valid_preconds(change, IFLAGS, log_file, quiet=False):
                continue

            harness_path = f"{harness_dir}/{change.old.ident.spelling}{CONFIG.IDENTITY_HARNESS}.c"
            function_state = ARG_STATES[func_name] if func_name in ARG_STATES \
                    else FunctionState()
            tu_includes = TU_INCLUDES[change.old.filepath] if \
                        change.old.filepath in TU_INCLUDES else \
                        ([],[])
            i_flags     = ' '.join(IFLAGS[change.old.filepath]).strip()

            if CONFIG.USE_EXISTING_DRIVERS and os.path.exists(harness_path):
                pass # Use existing driver
            else:
                create_harness(change, harness_path, tu_includes,
                    function_state, identity=True
                )
            # Run the identity harness
            if run_harness(change, script_env, harness_path, func_name, \
               log_file, i+1, total, i_flags, \
               quiet = CONFIG.SILENT_IDENTITY_VERIFICATION):

                harness_path = f"{harness_dir}/{change.old.ident.spelling}.c"

                if CONFIG.USE_EXISTING_DRIVERS and os.path.exists(harness_path):
                    pass # Use existing driver
                else:
                    create_harness(change, harness_path, tu_includes,
                        function_state, identity=False
                    )
                # Run the actual harness
                if run_harness(change, script_env, harness_path, func_name, log_file, \
                   i+1, total, i_flags, quiet = CONFIG.SILENT_VERIFICATION):
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
    os.chdir(dep_new)

    for _ in range(CONFIG.TRANSATIVE_PASSES):
        try:
            with multiprocessing.Pool(CONFIG.NPROC) as p:
                TRANSATIVE_CHANGED_FUNCTIONS       = flatten_dict(p.map(
                    partial(get_transative_changes_from_file,
                        changed_functions = CHANGED_FUNCTIONS,
                        dep_root_dir = dep_source_root_new
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


    impact_stage(LOG_DIR, PROJECT_SOURCE_FILES, CHANGED_FUNCTIONS)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be generated for both the project and the dependency."
    )
    parser.add_argument("--config", metavar="json", type=str, required=True,
        default="", help="JSON file containing a custom Config object to use")
    parser.add_argument("--diff", action='store_true', default=False,
        help='Print the first point of divergence for each function in the change set followed by the git-diff of the corresponding files and exit')

    args = parser.parse_args()
    CONFIG.update_from_file(args.config)
    CONFIG.SHOW_DIFFS = args.diff # Ignored if given in config file
    if CONFIG.VERBOSITY >= 2:
        pprint(CONFIG)

    run()

    sys.exit(0)

