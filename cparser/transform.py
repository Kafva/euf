from copy import deepcopy
from datetime import datetime
from functools import partial
import multiprocessing
import subprocess, os, sys, traceback
from clang import cindex
from typing import Set
from git.repo import Repo
from cparser.util import print_err, print_info
from cparser import BASE_DIR, CONFIG

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_top_level_decls(cursor: cindex.Cursor) -> Set[str]:
    ''' 
    Extract the names of all top level declerations (variables and functions) 
    excluding those defined externally under /usr/include
    
    '''
    global_decls: Set[str] = set()

    for child in cursor.get_children():
        if (str(child.kind).endswith("FUNCTION_DECL") or \
            str(child.kind).endswith("VAR_DECL") ) and \
            child.is_definition() and \
            not str(child.location.file).startswith("/usr/include"):
                global_decls.add(child.spelling)

    return global_decls

def get_clang_rename_args(basepath: str, ccdb: cindex.CompilationDatabase) -> tuple[Set[str], dict[str,list[str]], Set[str]]:
    '''
    Reads the compilation database and creates:
        1. A set of all top level labels in the changed files that we need to
        rename with a suffix
        2. A dict of compile command lists (with TU names as keys) for each TU to pass to `clang-rename`
        3. A list of the filepaths we should rename with `clang-rename`
    '''
    os.chdir(basepath)

    if CONFIG.VERBOSITY >= 1:
        start_time = datetime.now()

    global_names: Set[str] = set()
    commands: dict[str,list[str]] = {}
    filepaths: Set[str] = set()

    try:
        for ccmds in ccdb.getAllCompileCommands():
            # Depending on how the compile_commands.json is read
            # the full path may or may not be present...
            filepath = ccmds.filename

            # Skip files in other formats, e.g. asm
            if (not filepath.endswith(".c")) and (not filepath.endswith(".h")):
                continue

            if not filepath.startswith(basepath):
                filepath = basepath + "/" + filepath

            if filepath in filepaths:
                continue # Skip duplicate entries if they somehow appear
            else:
                filepaths.add(filepath)

            # For clang-rename we skip: -c -o <.o> <src>
            commands[filepath] = list(ccmds.arguments)[1:-4]

            try:
                # Exclude 'cc' [0] and source file [-1] from compile command
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = list(ccmds.arguments)[1:-1]
                )
                cursor: cindex.Cursor = tu.cursor
                global_names |= get_top_level_decls(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {basepath}/compile_commands.json")

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Argument generation execution time: {datetime.now() - start_time}") # type: ignore

    return (global_names, commands, filepaths)

def has_euf_internal_stash(repo: Repo, repo_name: str) -> str:
    '''
    Stashes are NOT per worktree so we need to check if each
    perticular old repo has its own stash or not

    Returns the stash@{x} string if the repository has a stash and
    an empty string otherwise
    '''
    for num,line in enumerate(repo.git.stash("list").splitlines()): # type: ignore
        if line.endswith(f"{CONFIG.CACHE_INTERNAL_STASH} {repo_name}"):
            return "stash@{" + str(num) + "}"

    return ""

def add_suffix_to_globals(dep_path: str, ccdb: cindex.CompilationDatabase,
        suffix: str = CONFIG.SUFFIX) -> bool:
    '''
    Go through every TU in the compilation database
    and save the top level declerations. 

    Then go through every source file and add a suffix
    to every occurence of the global symbols

    Renaming _all_ files in a big repository can take way to long so
    we limit ourselves to renaming the symbols from the files
    we know have changed. There will thus be duplicate symbols in both
    libraries but the functions that have been modified will still be
    differentiable
    '''

    dep_name = os.path.basename(dep_path)
    dep_repo = Repo(dep_path)

    if (stash_name := has_euf_internal_stash(dep_repo, dep_name)) != "":
        print_info(f"[{dep_name}] Using existing {stash_name} to add '{suffix}'")
        dep_repo.git.stash("apply", stash_name) # type: ignore
        return True

    print_info(f"Adding '{suffix}' suffixes to {dep_name}...")

    global_names, commands, _ = get_clang_rename_args(dep_path, ccdb)

    if len(global_names) == 0:
        print_err("No global names found")
        return False


    # * Dump a list of the global names to disk for the clang plugin 
    with open(CONFIG.RENAME_TXT, "w", encoding="utf8") as f:
        for name in list(global_names):
            f.write(name+'\n')

    # * Generate a list of all source files in the repo
    repo_files: list[str] = map(lambda f: f"{dep_path}/{f}",
            dep_repo.git.ls_tree(                        # type: ignore
            "-r", "HEAD", "--name-only").splitlines())   # type: ignore

    source_files = list(filter(lambda f:
        f.endswith(".c") or f.endswith(".h"), repo_files)) # types: ignore

    c_files = list(filter(lambda f: f.endswith(".c"), deepcopy(source_files)))
    h_files = list(filter(lambda f: f.endswith(".h"), deepcopy(source_files)))

    if CONFIG.VERBOSITY >= 1:
        start_time = datetime.now()

    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': CONFIG.RENAME_TXT,
        'SUFFIX': CONFIG.SUFFIX,
        'SETX': CONFIG.SETX,
        'PLUGIN': CONFIG.PLUGIN,
        'EXPAND': "true"
    })

    try:
        # * Run a Pool() subprocess job where each subprocess 
        #   is an invocation of:
        #       1. pcpp to expand macros for the file
        #       2. clang-suffix to perform the actual renaming
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            p.map(partial(call_clang_suffix,
                    script_env = script_env,
                    cwd = dep_path,
                    commands = commands
                ), c_files
            )
    except subprocess.CalledProcessError:
        traceback.print_exc()
        return False

    script_env.update({
        'CFLAGS': '',
        'EXPAND': "false"
    })

    # After renaming all symbols in source files, 
    # replace all global names inside header files
    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            p.map(partial(call_clang_suffix_headers,
                    script_env = script_env,
                    cwd = dep_path
                ), h_files
            )
    except subprocess.CalledProcessError:
        traceback.print_exc()
        return False

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Renaming execution time: {datetime.now() - start_time}") # type: ignore

    return True

def call_clang_suffix(source_file: str, script_env: dict[str,str], cwd: str,
        commands: dict[str,list[str]]):

    if not source_file in commands:
        return

    # * Determine the -isystem-flags for the perticular source file 
    isystem_flags = get_isystem_flags(source_file, cwd)

    cflags = get_clang_suffix_ccmds(commands[source_file])
    script_env.update({
        'INTERNAL_FLAGS': isystem_flags,
        'CFLAGS': ' '.join(cflags),
        'TARGET_FILE': source_file
    })

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Replacing global symbols in {source_file}")

    (subprocess.run([ f"{BASE_DIR}/scripts/clang-suffix.sh"  ],
        stdout = sys.stderr, cwd = cwd, env = script_env
    )).check_returncode()

def call_clang_suffix_headers(source_file: str, script_env: dict[str,str],
        cwd: str):

    # * Determine the -isystem-flags for the perticular source file 
    isystem_flags = get_isystem_flags(source_file, cwd)
    script_env.update({
        'INTERNAL_FLAGS': isystem_flags,
        'TARGET_FILE': source_file
    })

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Replacing global symbols in {source_file}")

    (subprocess.run([ f"{BASE_DIR}/scripts/clang-suffix.sh"  ],
        stdout = sys.stderr, cwd = cwd, env = script_env
    )).check_returncode()

def get_clang_suffix_ccmds(ccmds: list[str]):
    '''
    Only keep the `-I` and `-D` flags from the input
    '''
    clang_suffix_ccmds = []
    use_next = False

    for ccmd in ccmds:
        if use_next:
            clang_suffix_ccmds.append(ccmd)
            use_next = False
        elif ccmd.startswith("-D") or ccmd.startswith("-I"):
            clang_suffix_ccmds.append(ccmd)
            if ccmd == "-D" or ccmd == "-I": # If the symbol is given seperatly
                use_next = True

    return clang_suffix_ccmds

def get_isystem_flags(source_file: str, dep_path: str) -> str:
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
        f"clang -### {source_file} 2>&1 | sed '1,4d; s/\" \"/\", \"/g'",
        shell=True, cwd = dep_path
    ).decode('ascii').split(",")

    out = ""
    print_next = False

    for flag in isystem_flags:
        flag = flag.strip().strip('"')

        if flag == '-internal-isystem':
            out += " " + flag
            print_next = True
        elif print_next:
            out += " " + flag
            print_next = False

    return out.lstrip()
