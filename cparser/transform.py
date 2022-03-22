import subprocess, os, sys, traceback, multiprocessing, shutil, pynvim
from copy import deepcopy
from datetime import datetime
from functools import partial
from clang import cindex
from typing import Set
from git.repo import Repo
from cparser.macros import get_macros_from_file, update_macros_from_stub, \
        update_original_file_with_macros, write_macro_stub_file
from cparser.util import print_err, print_info
from cparser import BASE_DIR, CONFIG, IdentifierLocation

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_top_level_decl_locations(cursor: cindex.Cursor) -> Set[IdentifierLocation]:
    ''' 
    Extract the names of all top level declerations (variables and functions) 
    excluding those defined externally under /usr/include
    
    '''
    global_decls: Set[IdentifierLocation] = set()

    for child in cursor.get_children():
        if (str(child.kind).endswith("FUNCTION_DECL") or \
            str(child.kind).endswith("VAR_DECL") ) and \
            child.is_definition() and \
            not str(child.location.file).startswith("/usr/include"):
                global_decls.add(
                        IdentifierLocation.new_from_cursor(child)
                )

    return global_decls

def get_global_identifiers(basepath: str, ccdb: cindex.CompilationDatabase):
    '''
    Reads the compilation database and creates:
        A set of all top level labels in the changed files that we need to
        rename with a suffix as IdentifierLocation objects:
        filepath;global_name;line;col
    Note that the filepath refers to the file were the symbol was found,
    it can very well exist in more TUs
    '''
    os.chdir(basepath)

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Enumerating global symbols ({CONFIG.RENAME_CSV})")
        start_time = datetime.now()

    global_names: Set[IdentifierLocation] = set()
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

            try:
                # Exclude 'cc' [0] and source file [-1] from compile command
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = list(ccmds.arguments)[1:-1]
                )
                cursor: cindex.Cursor = tu.cursor
                global_names |= get_top_level_decl_locations(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {basepath}/compile_commands.json")

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Global symbol enumeration: {datetime.now() - start_time}") # type: ignore


    return global_names



def ensure_abs_path_in_includes(arguments: list[str]):
    '''
    Requires the cwd to be the directory of the source file being processed
    '''
    next_arg_is_path = False

    for i,arg in enumerate(arguments):
        if next_arg_is_path:
            arguments[i] = os.path.abspath(arg)
            next_arg_is_path = False
        if arg.startswith("-I"):
            if arg != "-I":
                arguments[i] = "-I" + os.path.abspath(arg[2:])
            else:
                next_arg_is_path = True

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

    '''
    dep_name = os.path.basename(dep_path)
    dep_repo = Repo(dep_path)

    if (stash_name := has_euf_internal_stash(dep_repo, dep_name)) != "":
        print_info(f"[{dep_name}] Using existing {stash_name} to add '{suffix}'")
        dep_repo.git.stash("apply", stash_name) # type: ignore
        return True

    print_info(f"Adding '{suffix}' suffixes to {dep_name}...")

    global_identifiers = get_global_identifiers(dep_path, ccdb)

    if len(global_identifiers) == 0:
        print_err("No global identifiers found")
        return False


    # * Dump a list of global_name;line;col names to disk 
    with open(CONFIG.RENAME_CSV, "w", encoding="utf8") as f:
        f.write("filepath;name;line;column\n")
        for identifier in global_identifiers:
            f.write(f"{identifier.to_csv()}\n")

    # * Generate a list of all source files in the repo
    repo_files: list[str] = map(lambda f: f"{dep_path}/{f}",
            dep_repo.git.ls_tree(                        # type: ignore
            "-r", "HEAD", "--name-only").splitlines())   # type: ignore

    source_files = list(filter(lambda f:
        f.endswith(".c") or f.endswith(".h"), repo_files)) # types: ignore

    c_files = list(filter(lambda f: f.endswith(".c"), deepcopy(source_files)))

    start_time: datetime = datetime.now()

    # Add _old suffixes to all globals in the old version
    #
    # ccls is able to rename symbols (cross-TU) while also taking macros
    # into consideration
    #
    # 1. Open ALL of the source files in vim
    #
    # 2. Go through each global symbol from /tmp/rename.csv
    # and place the cursor at the appropriate location 
    # 3. Initiate a rename of all occurrences


    # Open a standalone vim installation with lspconfig and ccls

    # Attach to the session
    #nvim = pynvim.attach()


    time_taken(start_time, "Renaming")

    return True

def replace_macros_in_file(source_file: str, script_env: dict[str,str],
        cwd: str, global_names: Set[str], dry_run: bool = False):

    macros    = get_macros_from_file(source_file)
    stub_file = write_macro_stub_file(source_file, macros)

    # Expand all macros in the stub file
    script_env.update({
        'EXPAND': "true"
    })

    # We will nearly always get errors when parsing a file with
    # macros that have been duct taped togheter
    try:
        call_clang_suffix_bare(stub_file, script_env, cwd, silent = True)
    except subprocess.CalledProcessError:
        traceback.print_exc()

    # Update the data property of each macro object
    # with the data from the stub file
    updated_macros = update_macros_from_stub(stub_file, macros, global_names, dry_run = dry_run)

    # Overwrite the original file with the updated macro data
    update_original_file_with_macros(source_file, updated_macros, dry_run)

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

def call_clang_suffix_bare(source_file: str, script_env: dict[str,str],
        cwd: str, silent: bool = False):

    # * Determine the -isystem-flags for the perticular source file 
    isystem_flags = get_isystem_flags(source_file, cwd)
    script_env.update({
        'INTERNAL_FLAGS': isystem_flags,
        'TARGET_FILE': source_file,
    })

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Replacing global symbols in {source_file}")

    if silent:
        out = subprocess.DEVNULL
    else:
        out = sys.stderr

    (subprocess.run([ f"{BASE_DIR}/scripts/clang-suffix.sh"  ],
        stdout = out, stderr = out, cwd = cwd, env = script_env
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
        f"clang -### {source_file} 2>&1 | sed -E '1,4d; s/\" \"/\", \"/g; s/(.*)(\\(in-process\\))(.*)/\\1\\3/'",
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

def read_in_names(rename_txt: str, names: Set[str]):
    with open(rename_txt, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            names.add(line.rstrip("\n"))

def time_taken(start_time: datetime, task: str):
    if CONFIG.VERBOSITY >= 1:
        print_info(f"[{task}] Done: {datetime.now() - start_time}")
        start_time = datetime.now()

