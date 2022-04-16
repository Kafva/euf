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

import subprocess, re, sys, json
from cparser import CONFIG, SubDirTU

def get_isystem_flags(source_file: str, dep_path: str) -> list:
    '''
    https://clang.llvm.org/docs/FAQ.html#id2
    The -cc1 flag is used to invoke the clang 'frontend', using only the
    frontend infers that default options are lost, errors like
    	'stddef.h' file not found
    are caused from the fact that the builtin-include path of clang is missing
    We can see the default frontend options used by clang with
    	clang -### test/file.cpp
    '''
    isystem_flags = subprocess.check_output(
        f"clang -### {source_file} 2>&1 | sed -E '1,4d; s/\" \"/\", \"/g; s/(.*)(\\(in-process\\))(.*)/\\1\\3/'",
        shell=True, cwd = dep_path
    ).decode('ascii').split(",")

    out = []
    add_next = False

    for flag in isystem_flags:
        flag = flag.strip().strip('"')

        if flag == '-internal-isystem':
            out.append(flag)
            add_next = True
        elif add_next:
            out.append(flag)
            add_next = False

    return out


def get_subdir_tus(target_dir: str) -> dict[str,SubDirTU]:
    '''
    Return a dict on the form { "subdir_path": subdir_tu }
    using a compile_commands.json as input. The ccdb_args array will
    contain the union of all compilation flags used for files in a subdir
    '''
    src_subdirs = dict()
    with open(f"{target_dir}/compile_commands.json", mode = 'r', encoding='utf8') as f:
        ccdb = json.load(f)

        for tu in ccdb:
            key = tu['directory'].rstrip("/")
            if not key in src_subdirs:
                subdir_tu = SubDirTU()
                subdir_tu.add_from_tu(tu)
                src_subdirs[key] = subdir_tu
            else:
                src_subdirs[key].add_from_tu(tu)

    return src_subdirs

def call_arg_states_plugin(target_dir: str, subdir: str, subdir_tu: SubDirTU,
        symbol_name: str, quiet:bool = True) -> None:
    '''
    Some of the ccdb arguments are not comptabile with the -cc1 frontend and need to
    be filtered out
    '''
    blacklist = r"|".join(CONFIG.ARG_STATES_COMPILE_FLAG_BLACKLIST)
    ccdb_filtered  = filter(lambda a: not re.match(blacklist, a), subdir_tu.ccdb_args)

    script_env = CONFIG.get_script_env()
    script_env.update({ CONFIG.ARG_STATES_OUT_DIR_ENV: CONFIG.ARG_STATES_OUTDIR })
    if quiet:
        out = subprocess.DEVNULL
    else:
        script_env.update({ CONFIG.ARG_STATES_DEBUG_ENV: "1" });
        out = sys.stderr


    # We assume that the isystem-flags are the same for all source files in a directory
    cmd = [ "clang", "-cc1", "-load", CONFIG.ARG_STATS_SO,
        "-plugin", "ArgStates", "-plugin-arg-ArgStates",
        "-symbol-name", "-plugin-arg-ArgStates", symbol_name ] + \
        get_isystem_flags(list(subdir_tu.files)[0], target_dir) + \
        list(subdir_tu.files) + [ "-I", "/usr/include" ] + list(ccdb_filtered)

    #print(f"({subdir})> \n", ' '.join(cmd))
    subprocess.run(cmd, cwd = subdir, stdout = out, stderr = out, env = script_env)

