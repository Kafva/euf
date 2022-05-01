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
from src.fmt import fmt_divergence, print_call_sites, print_changes, print_transistive_changes
from src.types import DependencyFunction, \
    DependencyFunctionChange, FunctionState, \
    CallSite, SourceDiff, SourceFile
from src.arg_states import join_arg_states_result, state_space_analysis
from src.harness import valid_preconds, create_harness, \
        get_I_flags_from_tu, run_harness, add_includes_from_tu
from src.util import ccdb_dir, flatten, flatten_dict, git_dir, git_relative_path, has_allowed_suffix, \
        mkdir_p, print_stage, remove_files_in, rm_f, time_end, time_start, \
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
 source_dir_old:str,
 dep_db_old: cindex.CompilationDatabase,
 source_dir_new:str,
 dep_db_new: cindex.CompilationDatabase) -> list[SourceDiff]:
    ''' Find the objects that correspond to the old and new commit '''
    (commit_old, commit_new) = get_commits(dep_repo)

    # Only include modified (M) and renamed (R) '.c' files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation:
    #   e.g. `foo.c -> src/foo.c`
    source_diffs = get_source_diffs(
            commit_old, source_dir_old, dep_db_old,
            commit_new, source_dir_new, dep_db_new
    )

    source_diffs = filter_out_excluded(source_diffs, \
        [ git_relative_path(d.filepath_old) for d in source_diffs ]
    )

    if not CONFIG.SKIP_BLAME:
        # Add additional diffs based on git-blame that were not recorded
        added_diff = list(filter(lambda d: \
                    has_allowed_suffix(d.a_path) and
                    'A' == d.change_type,
                commit_old.diff(commit_new) # type: ignore
        ))

        add_rename_changes_based_on_blame(
            added_diff, source_diffs,
            source_dir_old, dep_db_old,
            source_dir_new, dep_db_new
        )

    if CONFIG.VERBOSITY >= 1 and CONFIG.ONLY_ANALYZE == "":
        print_stage("Git Diff")
        out = ""
        for d in source_diffs:
            git_rel_old = git_relative_path(d.filepath_old)
            git_rel_new = git_relative_path(d.filepath_new)
            out += f"a/{git_rel_old} -> b/{git_rel_new}\n"

        print(out)
        wait_on_cr()

    return source_diffs

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
            changed_functions       = flatten(p.map(
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

        for d in source_diffs:
            cmd = ["git", # Force pager for every file
                "-c", "core.pager=less -+F -c",
                "diff", "--no-index", "--color=always",
                "-U20000",
                d.filepath_old,
                d.filepath_new ]
            print(' '.join(cmd))
            subprocess.run(cmd)

        sys.exit(0)

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

def reduction_stage(source_dir_old:str, source_dir_new:str,
 dep_db_old: cindex.CompilationDatabase,
 changed_functions: list[DependencyFunctionChange],
 source_diffs: list[SourceDiff],
 log_file: str):
    if CONFIG.VERBOSITY >= 1:
        print_stage("Reduction")

    global_identifiers, skip_renaming = \
            get_global_identifiers(source_dir_old, dep_db_old)

    write_rename_files(global_identifiers)

    # Compile the old and new version of the dependency as a set of 
    # goto-bin files
    if (new_lib := build_goto_lib(source_dir_new, new_version=True)) == "":
        sys.exit(ERR_EXIT)
    if (old_lib := build_goto_lib(source_dir_old, new_version=False)) == "":
        sys.exit(ERR_EXIT)

    # Copy any required headers into the include
    # directory of the driver
    os.makedirs(CONFIG.OUTDIR, exist_ok=True)

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
    remove_files_in(CONFIG.ARG_STATES_OUTDIR)

    rm_f(log_file)

    # Retrieve a list of the headers that each TU uses
    # We will need to include these in the driver
    # for types etc. to be defined
    IFLAGS = get_I_flags_from_tu(source_diffs, source_dir_old)

    # Exclude functions that we are not going to analyze
    changes_to_analyze = []
    for c in changed_functions:
        if valid_preconds(c,IFLAGS,skip_renaming,logfile="",quiet=True):
            changes_to_analyze.append(c)

    idents_to_analyze = [c.old.ident.location.name for c in changes_to_analyze]

    # Skip the state space analysis for static functions since these
    # cannot be called from the main project
    non_static_changes = [ c.old.ident.location.name for c in
            get_non_static(changes_to_analyze) ]

    state_space_analysis(idents_to_analyze, source_dir_old)
    #state_space_analysis(idents_to_analyze, source_dir_new)
    #state_space_analysis(non_static_changes, CONFIG.PROJECT_DIR)

    # Join the results from each analysis
    old_name    = os.path.basename(git_dir(new=False))
    new_name    = os.path.basename(git_dir(new=True))
    proj_name   = os.path.basename(CONFIG.PROJECT_DIR)
    ARG_STATES  = join_arg_states_result([ old_name, new_name, proj_name ])

    # - - - Harness generation - - - #
    harness_dir = f"{source_dir_old}/{CONFIG.HARNESS_DIR}"
    mkdir_p(harness_dir)

    TU_INCLUDES = {}
    total = len(changed_functions)

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
        add_includes_from_tu(diff, source_dir_old, IFLAGS, TU_INCLUDES)

    start = time_start("Starting change set reduction...")

    for i,change in enumerate(changed_functions[:]):
        # Begin by generating an identity driver and verify that it
        # passes as equivalent, then generate the actual driver and check if the
        # change is considered equivalent
        func_name = change.old.ident.location.name

        if CONFIG.ONLY_ANALYZE != "" and \
           CONFIG.ONLY_ANALYZE != func_name:
            continue

        # Log the reason for why a change could not be verified
        if not valid_preconds(change, IFLAGS, skip_renaming, \
           log_file, quiet=False):
            continue

        harness_path = f"{harness_dir}/{change.old.ident.location.name}{CONFIG.IDENTITY_HARNESS}.c"
        function_state = ARG_STATES[func_name] if func_name in ARG_STATES \
                else FunctionState()
        tu_includes = TU_INCLUDES[change.old.ident.location.filepath] if \
                    change.old.ident.location.filepath in TU_INCLUDES else \
                    ([],[])
        i_flags = ' '.join(IFLAGS[change.old.ident.location.filepath]).strip()

        if CONFIG.USE_EXISTING_DRIVERS and os.path.isfile(harness_path):
            pass # Use existing driver
        else:
            create_harness(change, harness_path, tu_includes,
                function_state, identity=True
            )
        # Run the identity harness
        if run_harness(change, script_env, harness_path, func_name, \
           log_file, i+1, total, i_flags, \
           quiet = CONFIG.SILENT_IDENTITY_VERIFICATION):

            harness_path = f"{harness_dir}/{change.old.ident.location.name}.c"

            if CONFIG.USE_EXISTING_DRIVERS and os.path.isfile(harness_path):
                pass # Use existing driver
            else:
                create_harness(change, harness_path, tu_includes,
                    function_state, identity=False
                )
            # Run the actual harness
            if run_harness(change, script_env, harness_path, func_name,
               log_file, i+1, total, i_flags,
               quiet = CONFIG.SILENT_VERIFICATION):
                # Remove the change from the change set 
                # if the equivalence check passes
                changed_functions.remove(change)

    time_end(f"Change set reduction: {total} -> {len(changed_functions)}",
                                                                          start)

def transitive_stage(source_dir_new:str,
 changed_functions: list[DependencyFunctionChange],
 dep_source_files: list[SourceFile], log_dir:str):
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
    TRANSATIVE_CHANGED_FUNCTIONS = {}
    os.chdir(git_dir(new=True))

    for _ in range(CONFIG.TRANSATIVE_PASSES):
        try:
            with multiprocessing.Pool(CONFIG.NPROC) as p:
                TRANSATIVE_CHANGED_FUNCTIONS       = flatten_dict(p.map(
                    partial(get_transative_changes_from_file,
                        changed_functions = changed_functions,
                        source_dir_new = source_dir_new
                    ),
                    dep_source_files
                ))
        except Exception:
            traceback.print_exc()
            sys.exit(ERR_EXIT)

        if CONFIG.VERBOSITY >= 1:
            print_transistive_changes(TRANSATIVE_CHANGED_FUNCTIONS)

        for key,calls in TRANSATIVE_CHANGED_FUNCTIONS.items():
            try:
                # Add calls to functions that have already been identified as changed
                if (idx := [ c.new for c in changed_functions ].index(key)):
                    changed_functions[idx].invokes_changed_functions.extend(calls)
            except ValueError:
                # Add a new function (with an indirect change) to the changed set
                changed_function = DependencyFunctionChange(
                        old = DependencyFunction.empty(),
                        new = key,
                        invokes_changed_functions = calls,
                        direct_change = False
                )
                changed_functions.append(changed_function)

    # Ensure a canonical order
    changed_functions = sorted(changed_functions,
            key = lambda c: c.old.ident.location.name
    )
    log_changed_functions(changed_functions, f"{log_dir}/trans_change_set.csv")

    if CONFIG.VERBOSITY >= 2:
        print_stage("Complete set")
        print_changes(changed_functions)
        time_end("Transitive change enumeration", start) # type: ignore

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

    if CONFIG.VERBOSITY >= 2 or len(call_sites) == 0:
        print_call_sites(call_sites)
    else:
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

    source_dir_old = ccdb_dir(new=False)
    source_dir_new = ccdb_dir(new=True)

    dep_repo = Repo(CONFIG.DEPENDENCY_DIR)

    if CONFIG.ENABLE_RESULT_LOG:
        mkdir_p(log_dir)

    mkdir_p(CONFIG.EUF_CACHE)
    mkdir_p(CONFIG.RESULTS_DIR)
    mkdir_p(CONFIG.ARG_STATES_OUTDIR)

    try:
        _ = dep_repo.active_branch
    except TypeError as e:
        print_err("Unable to read current branch name for" + \
            f" {CONFIG.DEPENDENCY_DIR}\n{e}"
        )
        sys.exit(1)

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    if not create_worktree(git_dir(new=False), CONFIG.COMMIT_NEW, dep_repo):
        sys.exit(ERR_EXIT)
    if not create_worktree(git_dir(new=True), CONFIG.COMMIT_OLD, dep_repo):
        sys.exit(ERR_EXIT)

    # Attempt to create the compilation database automatically
    # if they do not already exist
    dep_db_new = create_ccdb(source_dir_new)
    dep_db_old = create_ccdb(source_dir_old)
    main_db = create_ccdb(CONFIG.PROJECT_DIR)

    # Gather a list of all the source files in the main project
    project_files = get_source_files(CONFIG.PROJECT_DIR, CONFIG.PROJECT_DIR,
                                                                        main_db)

    # Create a list of all files from the dependency
    # used for transitive call analysis and state space estimation
    dep_source_files = get_source_files(git_dir(new=False), source_dir_old, dep_db_old)

    # - - - Git diff - - - #
    source_diffs = git_diff_stage(dep_repo,
        source_dir_old = source_dir_old,
        dep_db_old = dep_db_old,
        source_dir_new = source_dir_new,
        dep_db_new = dep_db_new
    )
    # - - - Change set - - - #
    changed_functions = ast_diff_stage(source_diffs, log_dir)

    # - - - Reduction of change set - - - #
    if CONFIG.FULL:
        log_file = f"{log_dir}/cbmc.csv"
        reduction_stage(
             source_dir_old,
             source_dir_new,
             dep_db_old,
             changed_functions,
             source_diffs,
             log_file
        )
        log_changed_functions(changed_functions, f"{log_dir}/reduced_set.csv")

    if CONFIG.SKIP_IMPACT:
        return (changed_functions, None)

    # - - - Transitive change set propagation - - - #
    transitive_stage(
        source_dir_new,
        changed_functions,
        dep_source_files,
        log_dir
    )
    # - - - Impact set  - - - #
    call_sites = impact_stage(log_dir, project_files, changed_functions)

    return (changed_functions, call_sites)

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
    if CONFIG.VERBOSITY >= 3:
        pprint(CONFIG)

    run()

    sys.exit(0)

