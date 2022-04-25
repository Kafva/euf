#!/usr/bin/env python3
'''
We will run the plugin once PER changed name PER source directory
If we try to run if once per changed named the include paths become inconsisitent between TUs
Running the plugin for all names (and once per file) is a bad idea as seen with the uber hack macros
in clang-plugins.

For this to work we need to create a union of all the ccmd flags for each directory

1. Split up the dep dir into subdirs (including top level)
2. Iterate over CHANGED_FUNCTIONS and call for each name ONCE per directory
'''
import subprocess, re, sys, json, os, traceback, multiprocessing
from functools import partial
from src import ERR_EXIT
from src.config import CONFIG
from src.types import SourceFile, FunctionState, SubDirTU
from src.util import mkdir_p, print_info, print_warn, \
        print_err, remove_files_in, time_end, time_start

def matches_excluded(string: str) -> bool:
    for exclude_regex in CONFIG.EXCLUDE_REGEXES:
        try:
            if re.search(rf"{exclude_regex}", string):
                return True
        except re.error:
            print_err(f"Invalid regex provided: {exclude_regex}")
            traceback.print_exc()
            sys.exit(ERR_EXIT)
    return False

def get_subdir_tus(target_source_dir: str, target_dir: str) -> dict[str,SubDirTU]:
    '''
    Return a dict on the form { "subdir_path": subdir_tu }
    using a compile_commands.json as input. The ccdb_args array will
    contain the union of all compilation flags used for files in a subdir
    '''
    src_subdirs = dict()
    with open(f"{target_source_dir}/compile_commands.json", mode = 'r', encoding='utf8') as f:
        ccdb = json.load(f)

        for tu in ccdb:
            # The exclude regex is given on the form "src/sub/.*"
            to_match = tu['directory']\
                .removeprefix(target_dir).removeprefix("/") + "/"

            if matches_excluded(to_match):
                continue

            key = tu['directory'].rstrip("/")

            if not key in src_subdirs:
                subdir_tu = SubDirTU()
                subdir_tu.add_from_tu(tu)
                src_subdirs[key] = subdir_tu
            else:
                src_subdirs[key].add_from_tu(tu)

    return src_subdirs

def call_arg_states_plugin(symbol_name: str, outdir:str, target_dir: str, subdir: str,
    subdir_tu: SubDirTU, quiet:bool = True) -> None:
    '''
    Some of the ccdb arguments are not comptabile with the -cc1 frontend and need to
    be filtered out.

    Different output directories can be provided to allow for non-overlapping filenames
    when analysing old/new versions of a dependency
    '''
    blacklist = r"|".join(CONFIG.ARG_STATES_COMPILE_FLAG_BLACKLIST)
    ccdb_filtered  = filter(lambda a: not re.match(blacklist, a), subdir_tu.ccdb_args)

    script_env = CONFIG.get_script_env()
    script_env.update({
        CONFIG.ARG_STATES_OUT_DIR_ENV: outdir
    })
    if quiet:
        out = subprocess.DEVNULL
    else:
        script_env.update({ CONFIG.ARG_STATES_DEBUG_ENV: "1" });
        out = sys.stderr


    # We assume that the isystem-flags are the same for all source files in a directory
    cmd = [ "clang", "-cc1", "-load", CONFIG.ARG_STATS_SO,
        "-plugin", "ArgStates", "-plugin-arg-ArgStates",
        "-symbol-name", "-plugin-arg-ArgStates", symbol_name ] + \
        SourceFile.get_isystem_flags(list(subdir_tu.files)[0], target_dir) + \
        list(subdir_tu.files) + [ "-I", "/usr/include" ] + list(ccdb_filtered)

    #print(f"({subdir})> \n", ' '.join(cmd))
    subprocess.run(cmd, cwd = subdir, stdout = out, stderr = out, env = script_env)

def join_arg_states_result(subdir_names: list[str]) -> dict[str,FunctionState]:
    '''
    The argStates clang plugin will produce one output file per TU for each CHANGED_FUNCTION
    (provided that the function in question was actually called in the TU) on the format
    <function_name>_<filename>.json:

        {
          "function_name": {
            "param_a": [],
            "param_b": [],
          }
        }

    If the same function is called from several files (in different subdirs), we need to combine
    these json objects into one. NOTE that an empty array means that the parameter was determined to be
    nondet(). The combined json will thus only have the union of fields if neither one is empty

    We limit the analysis to explicitly specified subdirectories to avoid issues when analysing
    multiple projects
    '''

    arg_states: dict[str,FunctionState] = {}

    for state_dir in subdir_names:
        dirpath = f"{CONFIG.ARG_STATES_OUTDIR}/{state_dir}"
        if not os.path.isdir(dirpath):
            print_warn(f"Missing state directory: {state_dir}")
            continue

        for state_file in os.listdir(dirpath):
            filepath = f"{dirpath}/{state_file}"

            with open(filepath, mode='r', encoding='utf8') as f:
                (function_name, params) = next(iter(json.load(f).items()))
                try:
                    idx=0
                    for param_name,values in params.items():

                        if not function_name in arg_states:
                            arg_states[function_name] = FunctionState()

                        # The parameters are guaranteed to be in order
                        arg_states[function_name].add_state_values(param_name, idx, set(values))
                        idx+=1

                except IndexError:
                    print_err(f"Empty state file: {filepath}")
                continue

    if CONFIG.VERBOSITY >= 2:
        # Show all parameters that were identified to have a
        # limited state space
        state_dirs = ' '.join(subdir_names)

        print_info(f"State space ({state_dirs}):")
        INDENT = CONFIG.INDENT

        for func_name,func_state in arg_states.items():
            if any([ not p.nondet for p in func_state.parameters ]):
                print(f"{func_name}()")

            for idx,param in enumerate(func_state.parameters):
                if not param.nondet:
                    print(f"\033[32m!>\033[0m{INDENT}{idx}.{param.name} = ", end='')
                    print(param.states)

    return arg_states

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
