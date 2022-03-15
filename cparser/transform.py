from datetime import datetime
import re
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

def replace_identifiers(input_file: str, global_names: list[str], suffix: str):
    '''
    I have tried `clang-rename` (does not consider macros and is single-threaded)
    I have tried `sed` (hard to avoid replacements inside strings)
    Writing a solution in Python...

    Go through each line in the input file:
        1. Skip over comment blocks and multiline strings
        2. On regular lines, split the line into STR and NOTSTR items

            char* myself = "myself"; printf("How does \"%s\" explain myself?", myself);
        => [ 'char* myself = ', 'myself', '; printf(', 'How do "%s" explain myself?", ', myself);' ]

        3. Replace identifers inside the NONSTR items and join the result into the newline

    This method does not consider usage of doubly enclosed strings...
    '''

    DELIM = "[^_0-9a-zA-Z]"

    with open(input_file, mode="r+", encoding='utf8') as f:
        inside_string = False
        inside_comment = False

        for line in f.readlines():
            if inside_comment:
                if res := re.search(r"\*/", line):
                    # Parse from res.end()
                    line = line[res.end():]
                else:
                    continue
            elif inside_string:
                pass

            # TODO: skip
            # ^\s*(#\s*include|\/\/

            #if re.search()

            # First split on escaped quotes
            escaped_split = line.split('\\"')

            # Unless the line starts with an unescaped quote (barring whitespace)
            # the first item will be a NOT_QOUTE_STR item
            if not line.lstrip().startswith('\\"'):
                not_qoute_str_idx = 0
            else:
                not_qoute_str_idx = 1

            # Iterate over the NOT_QOUTE_STR items
            # and split each one into STR, NOTSTR items
            for i in range(not_qoute_str_idx,len(escaped_split),2):
                string_split = escaped_split[i].split('"')


                # The first item will be a NOSTR item unless the main item
                # starts with a '"'
                if not escaped_split[i].lstrip().startswith('"'):
                    not_str_idx = 0
                else:
                    not_str_idx = 1
                print("[SPLIT]", string_split)

                # We can now go through the NOTSTR items and replace any 
                # occurrences of a global identifier
                for j in range(not_str_idx,len(string_split),2):

                    for name in global_names:
                        string_split[j] = \
                                re.sub(
                                    pattern = rf"({DELIM}|^)({name})({DELIM}|$)",
                                    repl = rf"\1\2{suffix}\3",
                                    string = string_split[j]
                                )


                # After replacing all occurrences of any identifier
                # overwrite the previous value
                # TODO: ensure that the '"' is inserted back correctly
                escaped_split[i] = '"'.join(string_split)

            print(">>> " +  '\\"'.join(escaped_split), end='')
            print(line, end='')


def add_suffix_to_globals(dep_path: str, ccdb: cindex.CompilationDatabase, suffix: str = CONFIG.SUFFIX) -> bool:
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

    global_names, _, _ = get_clang_rename_args(dep_path, ccdb)

    if len(global_names) == 0:
        print_err("No global names found")
        return False

    # Generate a Qualified -> NewName YAML file with translations for all of the
    # identified symbols
    with open(CONFIG.RENAME_YML, "w", encoding="utf8") as f:
        f.write("---\n")
        for name in list(global_names):
            f.write(f"- QualifiedName: {name}\n  NewName: {name}{suffix}\n")

    if CONFIG.VERBOSITY >= 1:
        start_time = datetime.now()

    try:
        # `clang-rename` does not work for references inside macros and
        # we therefore rely on 'sed' to perform replacements
        script_env = os.environ.copy()
        script_env.update({
            'RENAME_YML': CONFIG.RENAME_YML,
            'SUFFIX': CONFIG.SUFFIX,
            'VERBOSE': "true" if CONFIG.VERBOSITY >= 2 else "false"
        })
        (subprocess.run([ f"{BASE_DIR}/scripts/replace.sh"  ],
            stdout = sys.stderr, cwd = dep_path, env = script_env
        )).check_returncode()
    except subprocess.CalledProcessError:
        traceback.print_exc()
        sys.exit(-1)

    if CONFIG.VERBOSITY >= 1:
        print_info(f"Renaming execution time: {datetime.now() - start_time}") # type: ignore

    return True
