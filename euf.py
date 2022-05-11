#!/usr/bin/env python3
'''
1. Determine what source files in the dependency have been
modified (M) or renamed (R) since the last commit based on git labeling
2. Walk the AST of the old and new version of each modified file
3. Consider any functions with a difference in the AST composition as
the base change-set
4. Perform a configurable number of passes where we add functions that
are transitively changed, i.e. functions that call a function that
has been changed
5. Inspect all calls in the dependency to the changed functions and
save 'state sets' for each parameter. The state set will contain all
constant values that the given parameter can be assigned during program
execution or be set as empty if the parameter receives nondet() assignments
5. Analyze each of the objects in the base change-set and
remove equivalent entries based on CBMC analysis
6. Walk the AST of all source files in the main project and return
all locations were functions from the change set are called
'''
import argparse, sys, os, traceback, multiprocessing, subprocess
from datetime import datetime
from functools import partial
from pprint import pprint
from clang import cindex
from git.repo import Repo

from src import BASE_DIR, ERR_EXIT
from src.config import CONFIG
from src.fmt import fmt_divergence, print_call_sites, \
        print_changes, print_transistive_changes
from src.types import DependencyFunction, \
    DependencyFunctionChange, FunctionState, \
    CallSite, SourceDiff, SourceFile
from src.arg_states import join_arg_states_result, state_space_analysis
from src.harness import valid_preconds, create_harness, \
        get_include_paths_for_tu, run_harness, add_includes_from_tu
from src.util import ccdb_dir, flatten, flatten_dict, \
        git_dir, git_relative_path, has_allowed_suffix, \
        mkdir_p, print_stage, rm_f, time_end, time_start, \
        wait_on_cr, print_err, set_libclang
from src.change_set import add_rename_changes_based_on_blame, \
        get_changed_functions_from_diff, get_non_static, \
        get_transative_changes_from_file, log_changed_functions
from src.impact_set import get_call_sites_from_file, log_impact_set, \
        pretty_print_impact_by_call_site, pretty_print_impact_by_dep
from src.build import build_goto_lib, create_ccdb
from src.enumerate_globals import get_global_identifiers, write_rename_files
from src.scm import filter_out_excluded, get_commits, get_source_files, \
        get_source_diffs, create_worktree

def git_diff_stage(dep_repo: Repo,
 dep_db_old: cindex.CompilationDatabase,
 dep_db_new: cindex.CompilationDatabase) -> list[SourceDiff]:
    ''' Find the objects that correspond to the old and new commit '''
    (commit_old, commit_new) = get_commits(dep_repo)

    # Only include modified (M) and renamed (R) source files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation:
    #   e.g. `foo.c -> src/foo.c`
    source_diffs = get_source_diffs(commit_old, dep_db_old,
            commit_new, dep_db_new
    )

    source_diffs = filter_out_excluded(source_diffs, \
        [ git_relative_path(d.filepath_old) for d in source_diffs ]
    )

    if not CONFIG.SKIP_BLAME:
        # Add additional diffs based on git-blame that were not recorded
        # Note that we limit ourselves to files in SUFFIX_WHITELIST, i.e.
        # we only consider .c files
        added_diff = list(filter(lambda d: \
                    has_allowed_suffix(d.a_path, git_diff=False) and
                    'A' == d.change_type,
                commit_old.diff(commit_new) # type: ignore
        ))

        add_rename_changes_based_on_blame(added_diff, source_diffs,
            dep_db_old,
            dep_db_new
        )


    if CONFIG.SHOW_DIFFS:
        for d in source_diffs:
            cmd = ["git", # Force pager for every file
                "-c", "core.pager=less -+F -c",
                "diff", "--no-index", "--color=always",
                "-U20000",
                d.filepath_old,
                d.filepath_new ]
            print(' '.join(cmd))
            subprocess.run(cmd)
        # We also run part of the ast_diff_stage when this option is passed
        # to show divergences

    elif CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Git Diff")
        out = ""
        for d in source_diffs:
            git_rel_old = git_relative_path(d.filepath_old)
            git_rel_new = git_relative_path(d.filepath_new)
            out += f"a/{git_rel_old} -> b/{git_rel_new}\n"

        print(out)
        wait_on_cr()

    # Remove any header files from the diff list after passing the
    # diffing stage
    source_diffs = filter(lambda d:
            has_allowed_suffix(d.filepath_new), source_diffs
    )

    return list(source_diffs)

def ast_diff_stage(source_diffs: list[SourceDiff], log_dir: str) \
 -> list[DependencyFunctionChange]:
    '''
    Look through the old and new version of each delta
    using NPROC parallel processes and save
    the changed functions to `changed_functions`
    '''
    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Change set")
        start = datetime.now()

    changed_functions = []
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            changed_functions = flatten(p.map(
                get_changed_functions_from_diff,
                source_diffs
            ))
            changed_functions = list(filter(lambda f: \
                    not f.old.ident.location.name in CONFIG.IGNORE_FUNCTIONS,
                changed_functions[:]))

            if CONFIG.VERBOSITY >= 1 and \
               CONFIG.ONLY_ANALYZE == "" and not CONFIG.SHOW_DIFFS:
                print_changes(changed_functions)
    except Exception:
        traceback.print_exc()
        sys.exit(ERR_EXIT)

    os.chdir(BASE_DIR) # cwd changes during compilation

    if CONFIG.SHOW_DIFFS:
        for c in changed_functions:
            print(fmt_divergence(c))
        wait_on_cr(always=True)
        sys.exit(0) # !!

    if CONFIG.VERBOSITY >=1 and CONFIG.ONLY_ANALYZE == "":
        time_end("Finished change set enumeration", start) # type: ignore

    wait_on_cr()

    # Sort the functions to ensure that processing is always done
    # in the same order (makes testing easier)
    changed_functions = sorted(changed_functions,
            key = lambda c: c.old.ident.location.name
    )

    log_changed_functions(changed_functions, f"{log_dir}/change_set.csv")

    return changed_functions

def reduction_stage(
 dep_db_old: cindex.CompilationDatabase,
 changed_functions: list[DependencyFunctionChange],
 source_diffs: list[SourceDiff],
 log_dir: str):
    if CONFIG.VERBOSITY >= 1:
        print_stage("Reduction")

    total = len(changed_functions)

    global_identifiers, skip_renaming = \
            get_global_identifiers(ccdb_dir(new=False), dep_db_old)

    write_rename_files(global_identifiers)

    # Compile the old and new version of the dependency as a set of
    # goto-bin files
    if (new_lib := build_goto_lib(ccdb_dir(new=True), new_version=True))=="":
        sys.exit(ERR_EXIT)
    if (old_lib := build_goto_lib(ccdb_dir(new=False), new_version=False))=="":
        sys.exit(ERR_EXIT)

    # Copy any required headers into the include
    # directory of the driver
    os.makedirs(CONFIG.OUTDIR, exist_ok=True)

    name_old    = os.path.basename(git_dir(new=False))
    name_new    = os.path.basename(git_dir(new=True))
    name_proj   = os.path.basename(CONFIG.PROJECT_DIR)

    cbmc_log = f"{log_dir}/cbmc.csv"
    rm_f(cbmc_log)

    # Retrieve a list of the headers that each TU uses
    # We will need to include these in the driver
    # for types etc. to be defined
    include_paths = get_include_paths_for_tu(source_diffs, ccdb_dir(new=False))

    # - - - State space - - - #
    # Derive valid input parameters for each changed function based
    # on invocations in the old and new version of the dependency as
    # well as the main project This process is performed using an
    # external clang plugin.
    #
    # FIXME: If the main project has an internal function with the
    # same name as a function in the change set these will not
    # be differentiated and likely cause parameters to be set as
    # nondet when they could potentially be det.

    if CONFIG.ENABLE_STATE_SPACE_ANALYSIS:
        # Exclude functions that we are not going to analyze
        # Note: We make an exception for timed-out functions that are
        # present in blacklist.txt, it can still intresting to see the 
        # full state space analysis for these functions.
        changes_to_analyze = []
        for c in changed_functions:
            if valid_preconds(c,include_paths,skip_renaming,
                logfile="",quiet=True,
                ignore_timeout=True):
                changes_to_analyze.append(c)

        idents_to_analyze = [c.old.ident.location.name \
                for c in changes_to_analyze]

        # Skip the state space analysis for static functions since these
        # cannot be called from the main project
        non_static_changes = [ c.old.ident.location.name for c in
                get_non_static(changes_to_analyze) ]

        state_space_analysis(idents_to_analyze, ccdb_dir(new=False),
                                                name_old,log_dir)
        state_space_analysis(idents_to_analyze, ccdb_dir(new=True),
                                                name_new,log_dir)
        state_space_analysis(non_static_changes, CONFIG.PROJECT_DIR,
                                                 name_proj,log_dir)

        # Join the results from each analysis
        ARG_STATES  = join_arg_states_result([ name_old, name_new, name_proj ],
                log_dir)
    else:
        ARG_STATES = {}

    # - - - Harness generation - - - #
    harness_dir = f"{ccdb_dir(new=False)}/{CONFIG.HARNESS_DIR}"
    mkdir_p(harness_dir)

    # Holds a mapping from each source file in the dependency onto a list
    # of header files to include. The header files should be given with
    # paths relative to one of the '-I' paths for the TU in question
    tu_includes_dict = {}

    script_env = CONFIG.get_script_env()
    script_env.update({
        'NEW_LIB': new_lib,
        'OLD_LIB': old_lib,
        'OUTDIR': CONFIG.OUTDIR,
        'OUTFILE': CONFIG.CBMC_OUTFILE,
        'EUF_ENTRYPOINT': CONFIG.EUF_ENTRYPOINT,
        'CBMC_OPTS_STR': CONFIG.CBMC_OPTS_STR
    })

    for diff in source_diffs:
        add_includes_from_tu(diff, include_paths, tu_includes_dict)

    start = time_start("Starting change set reduction...")

    for i,change in enumerate(changed_functions[:]):
        # Begin by generating an identity driver and verify that it
        # passes as equivalent, then generate the actual driver and check if the
        # change is considered equivalent
        func_name = change.old.ident.location.name

        if CONFIG.ONLY_ANALYZE != "" and CONFIG.ONLY_ANALYZE != func_name:
            continue

        # Log the reason for why a change could not be verified
        if not valid_preconds(change, include_paths, skip_renaming, \
           cbmc_log, quiet=False):
            continue

        filepath_old = change.old.ident.location.filepath

        harness_path = f"{harness_dir}/{change.old.ident.location.name}"\
                       f"{CONFIG.IDENTITY_HARNESS}.c"
        function_state = ARG_STATES[func_name] if func_name in ARG_STATES \
                else FunctionState()
        tu_includes = tu_includes_dict[filepath_old] if \
                    filepath_old in tu_includes_dict else \
                    ([],[])
        run_include_paths = ' '.join(include_paths[filepath_old]).strip()

        if CONFIG.USE_EXISTING_DRIVERS and os.path.isfile(harness_path):
            pass # Use existing driver
        else:
            create_harness(change, harness_path, tu_includes,
                function_state, identity=True
            )
        # Run the identity harness
        success = run_harness(change, script_env, harness_path, func_name, \
           cbmc_log, i+1, total, run_include_paths, \
           identity=True, quiet = CONFIG.SILENT_IDENTITY_VERIFICATION
        )

        if success or CONFIG.IGNORE_FAILED_IDENTITY:
            harness_path = f"{harness_dir}/{change.old.ident.location.name}.c"

            if CONFIG.USE_EXISTING_DRIVERS and os.path.isfile(harness_path):
                pass # Use existing driver
            else:
                create_harness(change, harness_path, tu_includes,
                    function_state, identity=False
                )
            # Run the actual harness
            if run_harness(change, script_env, harness_path, func_name,
               cbmc_log, i+1, total, run_include_paths,
               identity=False, quiet = CONFIG.SILENT_VERIFICATION):
                # Remove the change from the change set
                # if the equivalence check passes
                changed_functions.remove(change)

    time_end(f"Change set reduction: {total} -> {len(changed_functions)}",
                                                                          start)

def transitive_stage(
 changed_functions: list[DependencyFunctionChange],
 dep_source_files_new: list[SourceFile], log_dir:str):
    '''
    To include functions that have not had a textual change but call a
    function that has changed, we perform a configurable number of
    additional passes were we look for invocations of changed functions
    in the dependency

    Note that we perform propagation after the reduction step
    We do not want to use CBMC analysis for transitive function calls

    We only need to look through the files in the new version
    '''
    if CONFIG.VERBOSITY >= 1:
        print_stage("Transitive change set")
        wait_on_cr()
        start = datetime.now()
    # Mapping from DependencyFunction -> list of called functions
    TRANSATIVE_CHANGED_FUNCTIONS = {}
    os.chdir(git_dir(new=True))

    for _ in range(CONFIG.TRANSATIVE_PASSES):
        try:
            with multiprocessing.Pool(CONFIG.NPROC) as p:
                TRANSATIVE_CHANGED_FUNCTIONS = flatten_dict(p.map(
                    partial(get_transative_changes_from_file,
                        changed_functions = changed_functions,
                    ),
                    dep_source_files_new
                ))
        except Exception:
            traceback.print_exc()
            sys.exit(ERR_EXIT)

        if CONFIG.VERBOSITY >= 1:
            print_transistive_changes(TRANSATIVE_CHANGED_FUNCTIONS)

        for func,calls in TRANSATIVE_CHANGED_FUNCTIONS.items():
            added = False
            for c in changed_functions:
                # Add calls to functions that have already
                # been identified as changed
                if c.new == func:
                    c.invokes_changed_functions |= set(calls)
                    added = True
                    break
            if not added:
                # Add a new function 
                # (with an indirect change) to the changed set
                changed_function = DependencyFunctionChange(
                        old = DependencyFunction.empty(),
                        new = func,
                        invokes_changed_functions = set(calls),
                        direct_change = False
                )
                changed_functions.append(changed_function)

    # Ensure a canonical order
    changed_functions = sorted(changed_functions,
            key = lambda c: c.old.ident.location.name
    )
    log_changed_functions(changed_functions, f"{log_dir}/trans_change_set.csv")

    if CONFIG.VERBOSITY >= 1:
        time_end("Transitive change enumeration", start) # type: ignore
    if CONFIG.VERBOSITY >= 3:
        print_stage("Complete set")
        print_changes(changed_functions)

def impact_stage(log_dir:str, project_source_files: list[SourceFile],
 changed_functions: list[DependencyFunctionChange]) -> list[CallSite]:
    ''' - - - Impact set - - - '''
    if CONFIG.VERBOSITY >= 1:
        print_stage("Impact set")
        wait_on_cr()
    call_sites: list[CallSite]      = []

    os.chdir(CONFIG.PROJECT_DIR)
    start = time_start("Enumerating call sites...")
    non_static_changes = get_non_static(changed_functions)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations (the impact set)
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            call_sites = flatten(p.map(
                partial(get_call_sites_from_file,
                    changed_functions = set(non_static_changes)
                ),
                project_source_files
            ))
    except Exception:
        traceback.print_exc()
        sys.exit(ERR_EXIT)

    time_end("Finished call site enumeration", start)

    if CONFIG.VERBOSITY >= 4 or len(call_sites) == 0:
        print_call_sites(call_sites)
    elif CONFIG.VERBOSITY >= 0:
        if CONFIG.ORDER_BY_CALL_SITE:
            pretty_print_impact_by_call_site(call_sites)
        else:
            pretty_print_impact_by_dep(call_sites)
    if CONFIG.ENABLE_RESULT_LOG:
        log_impact_set(call_sites, f"{log_dir}/impact_set.csv")

    return call_sites

def run(load_libclang:bool = True) -> tuple:
    '''
    Returns a tuple with changed functions and call_sites
    '''
    # - - - Setup - - -
    # Set the path to the clang library (platform dependent)
    # We need to skip this in tests where run() is invoked several times
    if load_libclang:
        set_libclang()

    dep_repo = Repo(CONFIG.DEPENDENCY_DIR)

    log_dir = f"{CONFIG.RESULTS_DIR}/{CONFIG.DEPLIB_NAME.removesuffix('.a')}"+\
        f"_{CONFIG.COMMIT_OLD[:4]}_{CONFIG.COMMIT_NEW[:4]}"

    dep_repo = Repo(CONFIG.DEPENDENCY_DIR)

    if CONFIG.ENABLE_RESULT_LOG:
        mkdir_p(log_dir)

    mkdir_p(CONFIG.EUF_CACHE)
    mkdir_p(CONFIG.RESULTS_DIR)
    mkdir_p(CONFIG.ARG_STATES_OUTDIR)

    try:
        _ = dep_repo.active_branch
    except TypeError as e:
        print_err("Unable to read current branch name for "
            f"{CONFIG.DEPENDENCY_DIR}\n{e}"
        )
        sys.exit(1)

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    if not create_worktree(git_dir(new=False), CONFIG.COMMIT_OLD, dep_repo):
        sys.exit(ERR_EXIT)
    if not create_worktree(git_dir(new=True), CONFIG.COMMIT_NEW, dep_repo):
        sys.exit(ERR_EXIT)

    # Attempt to create the compilation database automatically
    # if they do not already exist
    dep_db_old = create_ccdb(ccdb_dir(new=False))
    dep_db_new = create_ccdb(ccdb_dir(new=True))
    main_db = create_ccdb(CONFIG.PROJECT_DIR)

    # Gather a list of all the source files in the main project
    project_files = get_source_files(CONFIG.PROJECT_DIR, CONFIG.PROJECT_DIR,
                                                                        main_db)

    # Create a list of all files from the dependency
    # used for transitive call analysis and state space estimation
    dep_source_files_new = get_source_files(git_dir(new=True),
                                                ccdb_dir(new=True), dep_db_new)

    # - - - Git diff - - - #
    source_diffs = git_diff_stage(dep_repo,
        dep_db_old = dep_db_old,
        dep_db_new = dep_db_new
    )

    # - - - Change set - - - #
    changed_functions = ast_diff_stage(source_diffs, log_dir)

    # - - - Reduction of change set - - - #
    if CONFIG.FULL:
        reduction_stage(
             dep_db_old,
             changed_functions,
             source_diffs,
             log_dir
        )
        log_changed_functions(changed_functions, f"{log_dir}/reduced_set.csv")

    if CONFIG.SKIP_IMPACT:
        return (changed_functions, None)

    # - - - Transitive change set propagation - - - #
    transitive_stage(
        changed_functions,
        dep_source_files_new,
        log_dir
    )
    # - - - Impact set  - - - #
    call_sites = impact_stage(log_dir, project_files, changed_functions)

    return (changed_functions, call_sites)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be generated for both the project "
    "and the dependency."
    )
    parser.add_argument("-c", "--config", metavar="json", type=str,
        required=True, default="", help="JSON configuration file, "
        "refer to src/config.py for a list of available options.")
    parser.add_argument("-d", "--diff", action='store_true', default=False,
     help="Print the first point of divergence for each function in the "
     "change set followed by the git-diff of the corresponding files and exit"
    )

    args = parser.parse_args()
    CONFIG.update_from_file(args.config)
    CONFIG.SHOW_DIFFS = args.diff # Ignored if given in config file
    if CONFIG.VERBOSITY >= 3:
        pprint(CONFIG)

    if CONFIG.COMMIT_NEW == "" or CONFIG.COMMIT_OLD == "" or \
      CONFIG.PROJECT_DIR == "" or CONFIG.DEPENDENCY_DIR == "" or \
      CONFIG.DEPLIB_NAME == "":
        print_err("Missing obligatory option(s) in configuration file")
        sys.exit(ERR_EXIT)

    start_main = datetime.now()

    run()

    if CONFIG.VERBOSITY >= 1:
        time_end("Total runtime", start_main)

    sys.exit(0)

