import subprocess, os, traceback, pynvim, sys
from time import sleep
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
        if  str(child.kind).endswith("FUNCTION_DECL") and \
            child.is_definition() and \
            not str(child.location.file).startswith("/usr/include"):
        #if (str(child.kind).endswith("FUNCTION_DECL") or \
        #    str(child.kind).endswith("VAR_DECL") ) and \
        #    child.is_definition() and \
        #    not str(child.location.file).startswith("/usr/include"):
                global_decls.add(
                        IdentifierLocation.new_from_cursor(child)
                )

    return global_decls

def get_global_identifiers(basepath: str, ccdb: cindex.CompilationDatabase) -> Set[IdentifierLocation]:
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

    global_identifiers: Set[IdentifierLocation] = set()
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
                global_identifiers |= get_top_level_decl_locations(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {basepath}/compile_commands.json")


    time_end("Global symbol enumeration", start_time)

    if CONFIG.RENAME_BLACKLIST != "":
        blacklisted = set()
        read_in_names(CONFIG.RENAME_BLACKLIST, blacklisted)

        global_identifiers = set(list(filter(lambda ident:
            not ident.name in blacklisted, global_identifiers
        )))

    return global_identifiers

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
    into consideration. Note that ccls takes the compile_commands.json into account
    AND avoids renaming identifiers inside undefined code blocks i.e.
    #if 0
        // Things in here are not renamed
    #endif
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

    # (Debugging) Dump a list of global_name;line;col names to disk 
    with open(CONFIG.RENAME_CSV, "w", encoding="utf8") as f:
        f.write("filepath;name;line;column\n")
        for identifier in global_identifiers:
            f.write(f"{identifier.to_csv()}\n")


    # Generate a list of all source files in the repo
    repo_files: list[str] = map(lambda f: f"{dep_path}/{f}",
            dep_repo.git.ls_tree(                        # type: ignore
            "-r", "HEAD", "--name-only").splitlines())   # type: ignore

    source_files = list(filter(lambda f:
        f.endswith(".c") or f.endswith(".h"), repo_files)) # types: ignore

    GLOBALS_CNT = len(global_identifiers)

    script_env = os.environ.copy()
    script_env.update({
        'NVIM_LISTEN_ADDRESS': CONFIG.EUF_NVIM_SOCKET
    })

    out = sys.stderr if CONFIG.VERBOSITY >= 3 else subprocess.DEVNULL
    try:
        os.remove(CONFIG.EUF_NVIM_SOCKET)
    except OSError:
        pass

    # For the LSP to start properly we need to have a file from the project
    # open before we run any commands (this ensures that ccls is connected)
    #
    # Manually launching with pynvim.attach(argv) does not load ccls
    #
    # Example launch command:
    # NVIM_LISTEN_ADDRESS=/tmp/eufnvim  /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua --headless xml
    #
    # To support `argdo` commands we need to have all files open from the start
    p = subprocess.Popen([
        CONFIG.NVIM, '-n', '--clean', '-u', CONFIG.INIT_VIM,
        "--headless" ] + source_files,
        cwd = dep_path, env = script_env,
        stdout = out, stderr = out
    )

    start_time = time_start(f"Refactoring global symbols... ({GLOBALS_CNT})")

    macro_replace_symbols = list()
    longest_macro_name = max(map(lambda m: len(m), CONFIG.MACRO_NAMES))
    assert(longest_macro_name >= 1)

    # Wait for the socket (NVIM_LISTEN_ADDRESS) to be created
    sleep(3)

    try:
        with pynvim.attach('socket', path = CONFIG.EUF_NVIM_SOCKET) as nvim:

            for i,identifier in enumerate(global_identifiers):
                #if not identifier.filepath.endswith("xmltok_ns.c"): continue
                # Check if the identifier has a macro prefix
                base_symbol_name = identifier.name
                symbol_prefix = ""
                found = False

                for macro_name in CONFIG.MACRO_NAMES:
                    for prefix in macro_name['prefixes']:

                        if identifier.name.startswith(prefix):
                            base_symbol_name = identifier.name[ len(prefix): ]
                            symbol_prefix = prefix
                            found = True; break

                    if found: break

                if base_symbol_name != identifier.name:
                    if CONFIG.VERBOSITY >= 1:
                        print_info(f"[prefix-macro] Adding suffix to '{identifier}' ({i+1}/{GLOBALS_CNT})")

                    # We perform an exact string replace in _all_ source files 
                    # for 'PREFIX_MACRO(base_symbol_name)' after closing nvim
                    macro_replace_symbols.append({
                        'prefix': symbol_prefix,
                        'name': base_symbol_name
                    })
                else:
                    # Open the file where the global symbol was found
                    nvim.command(f"edit {identifier.filepath}")

                    # Move the cursor to the location of the identifier
                    nvim.call("cursor", identifier.line, identifier.column)

                    # If we are standing on a macro symbol (without a prefix)
                    # we will perform an exact match replacement instead of using ccls
                    text_to_replace = nvim.command_output(
                        f"echon getline('.')[col('.')-1:col('.')+{longest_macro_name}-1]"
                    )

                    if any(map(lambda m: text_to_replace.startswith(m['name']+"(") , CONFIG.MACRO_NAMES)): # type: ignore
                        if CONFIG.VERBOSITY >= 1:
                            print_info(f"[noop-macro] Adding suffix to '{identifier}' ({i+1}/{GLOBALS_CNT})")
                        macro_replace_symbols.append({
                            'prefix': "",
                            'name': identifier.name
                        })
                        continue

                    if CONFIG.VERBOSITY >= 1:
                        print_info(f"[ccls] Adding suffix to '{identifier}' ({i+1}/{GLOBALS_CNT})")

                    # Replace all occurrences of it cross-TUs
                    nvim.exec_lua(f"vim.lsp.buf.rename(\"{identifier.name + CONFIG.SUFFIX}\")")

                    # Short wait for every identifier to avoid inconsistent 
                    # behaviour? (We still get 
                    #   Vim(edit):E37: No write since last change 
                    # sometimes but generally the renaming works
                    sleep(3.0)

                    # We 'wa' and input <CR> sequences after each replace, otherwise 
                    # we get errors such as:
                    #   No write since last change (add ! to override)
                    # there is no problem if we run these commands to many times
                    nvim.feedkeys("<cr>"*100, escape_csi = True)

                    for _ in range(70):
                        nvim.command("wa")

                    sleep(1.5)

            # Closing the file will close the socket and generate an error
            try:
                nvim.command("quit")
            except OSError:
                    pass
    except pynvim.NvimError:
        traceback.print_exc()
        print_err("An error occurred during global refactoring")
        p.kill()
        return False

    p.kill()

    # Give a suffix to any macro_symbols that were encountered
    for source_file in source_files:
        for macro_name in CONFIG.MACRO_NAMES:
            needles = list(map(lambda sym:
                f"{macro_name['name']}({sym['name']})",
                macro_replace_symbols
            ))
            replacements = list(map(lambda sym:
                f"{macro_name['name']}({sym['name']}{CONFIG.SUFFIX})",
                macro_replace_symbols
            ))
            replace_in_file(source_file, needles, replacements)

    # If applicable, run the custom fix-up script to resolve any project
    # specific quirks
    if CONFIG.RENAME_SCRIPT != "":
        try:
            print_info(f"Running custom renaming script: {CONFIG.RENAME_SCRIPT}")
            script_env = CONFIG.get_script_env()
            script_env.update({ 'DEP_DIR_EUF': dep_path })
            subprocess.run([ CONFIG.RENAME_SCRIPT ],
                    env = script_env
            ).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
            print_err(f"Custom renaming script failed: {CONFIG.RENAME_SCRIPT}")
            return False

    if CONFIG.VERBOSITY >= 3:
        print("\n\n")

    time_end("Finished global symbol refactoring", start_time)

    return True

def time_start(msg: str) -> datetime:
    if CONFIG.VERBOSITY >= 1:
        print_info(msg)
    return datetime.now()

def time_end(msg: str, start_time: datetime) -> None:
    if CONFIG.VERBOSITY >= 1:
        print_info(f"{msg}: {datetime.now() - start_time}")
        start_time = datetime.now()

def replace_in_file(source_file: str, needles:list[str], replacements: list[str]):
        content = ""
        with open(source_file, "r", encoding = 'utf8') as f:
            content = f.read()
        with open(source_file, "w", encoding = 'utf8') as f:
            for i in range(len(needles)):
                content = content.replace(
                        needles[i], replacements[i]
                )
            f.write(content)
