from pathlib import Path
import subprocess, os, sys, traceback, multiprocessing, shutil, re
from copy import deepcopy
from datetime import datetime
from functools import partial
from clang import cindex
from typing import Set
from git.repo import Repo
from cparser.macros import get_macros_from_file, update_macros_from_stub, \
        update_original_file_with_macros, write_macro_stub_file
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
        print_info(f"Enumerating global symbols ({CONFIG.RENAME_TXT}) and generating ccmd list")
        start_time = datetime.now()

    global_names: Set[str] = set()
    commands: dict[str,list[str]] = {}
    filepaths: Set[str] = set()

    use_existing_names = False
    if os.path.exists(CONFIG.RENAME_TXT):
        print_info(f"Found preexisting {CONFIG.RENAME_TXT}: Skipping symbol enumeration")
        read_in_global_names(CONFIG.RENAME_TXT, global_names)
        use_existing_names = True

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
            arguments = list(ccmds.arguments)[1:-4]

            os.chdir(ccmds.directory)
            ensure_abs_path_in_includes(arguments)
            commands[filepath] = arguments
            os.chdir(basepath)

            try:
                # Exclude 'cc' [0] and source file [-1] from compile command
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = list(ccmds.arguments)[1:-1]
                )
                cursor: cindex.Cursor = tu.cursor
                if not use_existing_names:
                    global_names |= get_top_level_decls(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {basepath}/compile_commands.json")

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Global symbol enumeration: {datetime.now() - start_time}") # type: ignore



    return (global_names, commands, filepaths)

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

    start_time: datetime = datetime.now()

    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': CONFIG.RENAME_TXT,
        'SUFFIX': CONFIG.SUFFIX,
        'SETX': CONFIG.SETX,
        'PLUGIN': CONFIG.PLUGIN,
        'EXPAND': "false"
    })

    #-------------- Rename C,H and Macros seperatly ----------------#
    #if CONFIG.VERBOSITY >= 1:
    #    start_time_total = datetime.now()
    #h_files = list(filter(lambda f: f.endswith(".h"), deepcopy(source_files)))
    #
    #try:
    #    with multiprocessing.Pool(CONFIG.NPROC) as p:
    #        # Run a Pool() subprocess job where each subprocess 
    #        # is an invocation of clang-suffix to perform the actual renaming
    #        # of a specific file

    #        time_update(".c files", ".c files", len(c_files), start_time)
    #        p.map(partial(call_clang_suffix,
    #                script_env = script_env,
    #                cwd = dep_path,
    #                commands = commands
    #            ), c_files
    #        )
    #        time_update(".c files", "", -1, start_time)
    #except subprocess.CalledProcessError:
    #    print_err("Error occured for .c file renaming")
    #    traceback.print_exc()

    #script_env.update({
    #    'CFLAGS': '',
    #    'EXPAND': "false"
    #})

    #try:
    #    with multiprocessing.Pool(CONFIG.NPROC) as p:
    #        # 2. After renaming all symbols in .c files, 
    #        # replace all global names inside header files (silent errors)

    #        time_update(".c files", ".h files", len(h_files), start_time)
    #        p.map(partial(call_clang_suffix_bare,
    #                script_env = script_env,
    #                cwd = dep_path,
    #                silent = True
    #            ), h_files
    #        )
    #except subprocess.CalledProcessError:
    #    print_err("Error occured for .h file processing")
    #    traceback.print_exc()

    #try:
    #    with multiprocessing.Pool(CONFIG.NPROC) as p:
    #        # 3. Finally, go through all of the files (.c and .h) again and 
    #        # replace any global names present inside macros (this process 
    #        # does not handle macros that call macros defined in seperate files)

    #        time_update(".h files", "macros", len(source_files), start_time)
    #        p.map(partial(replace_macros_in_file,
    #                script_env = script_env,
    #                cwd = dep_path,
    #                global_names = global_names
    #            ), source_files
    #        )
    #        time_update("macros", "", -1, start_time)

    #except subprocess.CalledProcessError:
    #    print_err("Error occured for macro processing")
    #    traceback.print_exc()

    #if CONFIG.VERBOSITY >= 1:
    #    print_info(f"clang-suffix (total): {datetime.now() - start_time_total}") # type: ignore



    #-------------- Rename expanded C files ----------------#
    # OPENSSL: (hack)
    # Show current config: 
    #   perl configdata.pm -m
    # For pre-processing to work we need to configure
    # openssl correctly, otherwise we get errors e.g.
    #   include/openssl/macros.h:113:4: error: #error "OPENSSL_API_COMPAT expresses an impossible API compatibility level"
    #     113 | #  error "OPENSSL_API_COMPAT expresses an impossible API compatibility level"
    #
    # We can't do this immeidiatelly since compile_commands.json is not properply created with goto-cc
    #if re.search("openssl", dep_path) != None:
    #    try:
    #        (subprocess.run( [ f"{BASE_DIR}/scripts/ssl_prep.sh" ], cwd = dep_path )
    #            .check_returncode())
    #    except subprocess.CalledProcessError:
    #        traceback.print_exc()
    #        return False

    try:
        with multiprocessing.Pool(CONFIG.NPROC) as p:
            # 1. To fully rename all globals we need preprocessing to be ran on 
            # the files we perform replacements in, otherwise macros that 
            # access global identifiers will not be properly resolved
            time_update("", ".c files", len(c_files), start_time, "preprocessing")
            p.map(partial(preprocess_source_file,
                    script_env = script_env,
                    cwd = dep_path,
                    commands = commands
                ), c_files
            )
    except subprocess.CalledProcessError:
        print_err("Error occured for .c file preprocessing")
        traceback.print_exc()
        return False

    try:
        # OPENSSL:
        # For the parsing to work better it is preferable if one has
        # already built the project once with `make` since this
        # creates 'include/openssl/configuration.h' from 
        # 'include/openssl/configuration.h.in' which every step
        # otherwise complains about

        with multiprocessing.Pool(CONFIG.NPROC) as p:
            # 2. Run a Pool() subprocess job where each subprocess 
            # is an invocation of clang-suffix to perform the actual renaming
            # of a specific file

            time_update(".c files", ".c files", len(c_files), start_time)
            p.map(partial(call_clang_suffix,
                    script_env = script_env,
                    cwd = dep_path,
                    commands = commands
                ), c_files
            )
            time_update(".c files", "", -1, start_time)
    except subprocess.CalledProcessError:
        print_err("Error occured for .c file renaming")
        traceback.print_exc()


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

def preprocess_source_file(source_file: str, script_env: dict[str,str], cwd: str,
        commands: dict[str,list[str]]):

    if not source_file in commands.keys():
        print_err(f"Missing compilation instructions: {source_file}")
        return

    outfile = f"/tmp/E_{os.path.basename(source_file)}"

    # If we use `clang` here the includes become corrupted with things
    # that should not be there, e.g. typedef for _Float32
    #   /usr/include/bits/floatn-common.h:214:1: error: conflicting type modifiers
    #       typedef float _Float32;

    # TODO: The expat compile_commands.json does not include ./lib/xmltok_impl.c 
    # likely because it does not have a 'dedicated' target in the Makefile

    cmd = [ "goto-cc", "-E" ] + commands[source_file] + [ source_file, "-o", outfile ]
    if CONFIG.VERBOSITY >= 1:
        print_info(f"Processing {source_file}")
        print(' '.join(cmd))

    (subprocess.run(cmd,
        stdout = sys.stderr, cwd = cwd, env = script_env
    )).check_returncode()

    shutil.move(outfile, source_file)

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

def time_update(prev_step: str, next_step: str, next_step_cnt: int, start_time: datetime,
        task: str = "clang-suffix"):
    if CONFIG.VERBOSITY >= 1:
        if prev_step != "":
            print_info(f"Done ({prev_step}): {datetime.now() - start_time}")
        if next_step != "":
            print_info(f"Start: {task} ({next_step}): {next_step_cnt}")

        start_time = datetime.now()

def read_in_global_names(rename_txt: str, global_names: Set[str]):
    with open(rename_txt, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            global_names.add(line.rstrip("\n"))

