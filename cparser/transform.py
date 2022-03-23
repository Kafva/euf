import subprocess, os, traceback, pynvim, time
import sys
from datetime import datetime
from clang import cindex
from typing import Set
from git.repo import Repo

from cparser.util import print_err, print_info
from cparser import CONFIG, IdentifierLocation

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

    start_time = time_start(f"Enumerating global symbols...")

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


    time_end("Global symbol enumeration", start_time)

    return global_names

def read_in_names(rename_txt: str, names: Set[str]):
    with open(rename_txt, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            names.add(line.rstrip("\n"))

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

    ccls is able to rename symbols (cross-TU) while also taking macros
    into consideration
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

    # Example launch command:
    # NVIM_LISTEN_ADDRESS=/tmp/eufnvim  /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua --headless regexec.c

    GLOBALS_CNT = len(global_identifiers)
    start_time = time_start(f"Refactoring global symbols... ({GLOBALS_CNT})")

    source_file = next(iter(global_identifiers)).filepath

    script_env = os.environ.copy()
    script_env.update({
        'NVIM_LISTEN_ADDRESS': CONFIG.EUF_NVIM_SOCKET
    })

    out = sys.stderr if CONFIG.VERBOSITY >= 3 else subprocess.DEVNULL

    # For the LSP to start proerply we need to have a file from the project
    # open before we run any commands (this ensures that ccls is connected)
    #
    # Manually launching with pynvim.attach(argv) does not load ccls
    p = subprocess.Popen([
        CONFIG.NVIM, '-n', '--clean', '-u', CONFIG.INIT_VIM,
        "--headless", source_file ],
        cwd = dep_path, env = script_env,
        stdout = out, stderr = out
    )

    # Wait for the socket (NVIM_LISTEN_ADDRESS) to be created
    time.sleep(2)

    with pynvim.attach('socket', path = CONFIG.EUF_NVIM_SOCKET) as nvim:

        for i,identifier in enumerate(global_identifiers):
            #if not identifier.filepath.endswith("regexec.c"): continue

            # Open the file where the global symbol was found
            nvim.command(f"edit {identifier.filepath}")

            # Move the cursor to its location
            nvim.call("cursor", identifier.line, identifier.column)

            # Replace all occurences of it cross-TUs
            nvim.exec_lua(f"vim.lsp.buf.rename(\"{identifier.name + CONFIG.SUFFIX}\")")

            # We 'wa' and input <CR> sequences after each replace, otherwise 
            # we get errors such as:
            #   No write since last change (add ! to override)
            # there is no problem if we run these commands to many times
            crs = ''.join([ "<cr>" for _ in range(100) ])
            nvim.feedkeys(crs, escape_csi = True)

            for _ in range(50):
                nvim.command("wa")

            if CONFIG.VERBOSITY >= 1:
                print_info(f"Adding suffix to '{identifier.name}' ({i+1}/{GLOBALS_CNT})")

        # Closing the file will close the socket and generate an error
        try:
            nvim.command("quit")
        except OSError:
                pass


    if CONFIG.VERBOSITY >= 3:
        print("\n\n")

    time_end("Finished global symbol refactoring", start_time)
    p.terminate()

    return True

def time_start(msg: str) -> datetime:
    if CONFIG.VERBOSITY >= 1:
        print_info(msg)
    return datetime.now()

def time_end(msg: str, start_time: datetime) -> None:
    if CONFIG.VERBOSITY >= 1:
        print_info(f"{msg}: {datetime.now() - start_time}")
        start_time = datetime.now()
