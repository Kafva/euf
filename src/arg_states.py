#!/usr/bin/env python3
'''
We will run the plugin once PER changed name PER source directory
If we try to run the plugin once per changed named the include paths become 
inconsistent between TUs. Running the plugin for all names (and once per file) 
is a bad idea as seen with the uber hack macros in clang-plugins.

1. Split up the dependency dir into subdirs (including "." if applicable)
2. Iterate over CHANGED_FUNCTIONS and call for each name ONCE per directory
'''
import subprocess, re, sys, json, os, traceback, multiprocessing
from glob import glob
from functools import partial
from src import ERR_EXIT
from src.config import CONFIG
from src.types import SourceFile, FunctionState, SubDirTU
from src.util import git_relative_path, mkdir_p, print_info, print_warn, \
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

def get_subdir_tus(source_dir: str) -> dict[str,SubDirTU]:
    '''
    Return a dict on the form { "subdir_path": subdir_tu }
    using a compile_commands.json as input. The ccdb_args array will
    contain the union of all compilation flags used for files in a subdir

    Note: This assumes that the ccdb has flags with arguments, e.g.
    "-I include" given as a single item "-Iinclude"
    '''
    src_subdirs = {}
    with open(f"{source_dir}/compile_commands.json", mode = 'r', encoding='utf8') as f:
        ccdb = json.load(f)

        for tu in ccdb:
            # The exclude regex is given on the form "src/sub/.*"
            to_match = git_relative_path(tu['directory'])+"/"

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

def call_arg_states_plugin(symbol_name: str, outdir:str,
    subdir: str, subdir_tu: SubDirTU,
    quiet:bool = True, setx:bool=False) -> tuple[str,bool]:
    '''
    Some of the ccdb arguments are not compatible with the -cc1 
    frontend and need to be filtered out.

    Different output directories can be provided to allow for 
    non-overlapping filenames when analysing old/new versions of a dependency
    '''
    blacklist = r"|".join(CONFIG.ARG_STATES_COMPILE_FLAG_BLACKLIST)

    # Since the ccdb_args for SubDirTU objects are not read from 
    # SourceFile objects, we need to manually include any EXTRA_COMPILE_FLAGS
    #
    # Note the use of a list() and not a set(), it is preferable
    # for the arguments to be provided in the same order that they are written
    ccdb_arguments  = filter(lambda a: not re.match(blacklist, a),
                                list(subdir_tu.ccdb_args) +
                                CONFIG.EXTRA_COMPILE_FLAGS
                      )
    # There should not be a need to modify escaped '\' values
    # inside of ccdb_args, the ccdb has been improperly generated
    # if it solves issues to do so.
    script_env = CONFIG.get_script_env()
    script_env.update({
        CONFIG.ARG_STATES_OUT_DIR_ENV: outdir
    })

    if quiet:
        out = subprocess.PIPE
    else:
        script_env.update({ CONFIG.ARG_STATES_DEBUG_ENV: "1" })
        out = sys.stderr

    # We assume all headers that we need to analyze are included by one
    # or more of the c files so we do not explicitly pass them
    c_files = list(filter(lambda f: f.endswith(".c"), subdir_tu.files))

    # Use compile dir relative names to limit output size
    c_files = list(map(lambda f: f.removeprefix(subdir+"/"), c_files))

    # We assume that the isystem-flags are the same 
    # for all source files in a directory
    isystem_flags = SourceFile.get_isystem_flags(c_files[0], subdir)

    cmd = [ CONFIG.CCDB_CC,
        "-cc1", "-fcolor-diagnostics", "-load", CONFIG.ARG_STATS_SO,
        "-plugin", "ArgStates", "-plugin-arg-ArgStates",
        "-symbol-name", "-plugin-arg-ArgStates", symbol_name ] + \
         isystem_flags + c_files + [ "-I", "/usr/include" ] + \
         list(ccdb_arguments)

    cmd_str =' '.join(cmd)
    cmd_str = cmd_str[:CONFIG.CLANG_PLUGIN_RUN_STR_LIMIT] + "..." \
            if len(cmd_str) > CONFIG.CLANG_PLUGIN_RUN_STR_LIMIT \
            else cmd_str

    success = True
    output = ""
    try:
        p = subprocess.Popen(cmd, cwd = subdir, stdout = out, stderr = out,
                            env = script_env)
        p.wait()

        if quiet:
            stdout_txt = p.stdout.read().decode('utf8')  # type: ignore
            if len(stdout_txt) > 0:
                output = "====> stdout <====\n" + stdout_txt + "\n"

            stderr_txt = p.stderr.read().decode('utf8')  # type: ignore
            if len(stderr_txt) > 0:
                output += "====> stderr <====\n" + stderr_txt

        if p.returncode != 0:
            print_err(f"State space analysis failed: "
                      f"{p.returncode}\n({outdir},{symbol_name})"
            )
            if CONFIG.VERBOSITY >= 2 and len(output.splitlines()) > 0 and quiet:
                print(output,flush=True)
            success = False
    except FileNotFoundError:
        # Usually caused by faulty paths in ccdb
        traceback.print_exc()
        print_err("This error has likely occured due to invalid entries in " +
                "compile_commands.json")
        if quiet:
            print(output,flush=True)
        success = False

    if setx:
        print(f"({outdir},{symbol_name})\ncd {subdir}\n", cmd_str)

    return symbol_name, success

def join_arg_states_result(subdir_names: list[str]) -> dict[str,FunctionState]:
    '''
    The argStates clang plugin will produce one output file per TU for each 
    CHANGED_FUNCTION (provided that the function in question was actually 
    called in the TU) on the format
    <function_name>_<filename>.json:

        {
          "function_name": {
            "param_a": [],
            "param_b": [],
          }
        }

    If the same function is called from several files (in different subdirs), 
    we need to combine these json objects into one. NOTE that an empty array 
    means that the parameter was determined to be nondet(). The combined json 
    will thus only have the union of fields if neither one is empty

    We limit the analysis to explicitly specified subdirectories to avoid 
    issues when analysing multiple projects
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

    if CONFIG.VERBOSITY >= 1:
        # Show all parameters that were identified to have a
        # limited state space
        state_dirs = ' '.join(subdir_names)

        print_info(f"State space ({state_dirs}):")
        INDENT = CONFIG.INDENT

        for func_name,func_state in arg_states.items():
            if any(not p.nondet for p in func_state.parameters):
                print(f"{func_name}()")

            for idx,param in enumerate(func_state.parameters):
                if not param.nondet:
                    print(f"\033[32m!>\033[0m{INDENT}{idx}.{param.name} = ", end='')
                    print(param.states)

    return arg_states

def state_space_analysis(symbols: list[str], source_dir: str, target_name:str):

    start = time_start(f"Inspecting call sites ({target_name})...")

    # Remove any previously recorded states
    outdir = f"{CONFIG.ARG_STATES_OUTDIR}/{target_name}"
    mkdir_p(outdir)
    remove_files_in(outdir)

    subdir_tus = get_subdir_tus(source_dir)
    if CONFIG.VERBOSITY >= 3:
        print("Subdirectories to analyze: ", end='')
        print([ p.removeprefix(f"{source_dir}/")
                    for p in subdir_tus])

    with multiprocessing.Pool(CONFIG.NPROC) as p:
        for subdir, subdir_tu in subdir_tus.items():
            return_values = p.map(partial(call_arg_states_plugin,
                outdir = outdir,
                subdir = subdir,
                subdir_tu = subdir_tu,
                quiet = not CONFIG.DEBUG_CLANG_PLUGIN,
                setx = False),
                symbols
            )

            # If the ArgStates plugin fails to complete its analysis and crashes for a
            # symbol we need to exclude any assumptions about this symbol. E.g. if
            # analysis for the symbol 'foo' finds only constant values in one SubDirTU and
            # crashes for all others, we need to defensively assume that it could be 
            # non-det in one of the TUs we failed to analyze.
            failed_symbol_analysis = set()
            for tpl in return_values:
                if not tpl[1]:
                    failed_symbol_analysis.add(tpl[0])

            if len(failed_symbol_analysis)>0:
                if CONFIG.VERBOSITY>=1:
                    print_err(f"Incomplete state enumeration:")
                    print(failed_symbol_analysis)

                # Remove all state files created for symbols that could
                # not be fully analyzed
                for sym in failed_symbol_analysis:
                    for state_file in glob(f"{outdir}/{sym}*"):
                        if CONFIG.VERBOSITY>=1:
                            print_info(f"Removing {state_file}")
                        os.remove(state_file)

    time_end(f"State space analysis ({target_name})", start)
