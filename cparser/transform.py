from datetime import datetime
import subprocess, os, sys, traceback
from clang import cindex
from typing import Set
from git.repo import Repo
from cparser.util import print_err, print_info
from cparser import CONFIG

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

    To my knowledge, we cannot selectivly rename only the labels we need unless
    we create a custom library that prevents conflicts
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

def add_suffix_to_globals(dep_path: str, ccdb: cindex.CompilationDatabase, suffix: str = "_abcdefghijk") -> bool:
    '''
    Go through every TU in the compilation database
    and save the top level declerations. 

    Then go through every source file and add a suffix
    to every occurence of the global symbols using
    'clang-rename'

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

    global_names, commands, filepaths = get_clang_rename_args(dep_path, ccdb)

    if len(global_names) == 0:
        print_err("No global names found")
        return False

    # Generate a Qualified -> NewName YAML file with translations for all of the
    # identified symbols
    with open(CONFIG.RENAME_YML, "w", encoding="utf8") as f:
        f.write("---\n")
        for name in list(global_names):
            f.write(f"- QualifiedName: {name}\n  NewName: {name}{suffix}\n")

    # `clang-rename` renames symbols in the current .c file AND all headers were 
    # the symbol is referenced. This causes issues when other .c files reference 
    # the old name of a symbol that has been renamed in the headers
    #
    # To circumvent this we can individually rename the symbols in each .c file
    # TODO: If we patched the clang-rename program to not rename headers we 
    # could run these processes in parallel
    #   ./clang/tools/clang-rename/ClangRename.cpp
    #
    # clang-rename does not work for references inside macros...
    # It also seems like code inside false "#ifdefs" is not renamed
    # This should not be an issue if we compile with the same options though
    #
    # We end up having to basically rely on 'sed' to resolve this...
    # at which point we could just use 'sed' directly...
    if CONFIG.VERBOSITY >= 1:
        start_time = datetime.now()

    for filepath in filepaths:
        # Using --force will suppress all errors but still apply changes
        # we need this flag since not every file will have all symbols
        cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML, "--force", "-i",
            filepath, "--" ] + commands[filepath]

        if CONFIG.VERBOSITY >= 2:
            print(' '.join(cmd))
        try:
            (subprocess.run(cmd, cwd = dep_path,
            stdout = sys.stdout, stderr = sys.stderr
            )).check_returncode()

            # Restore any changes made to headers
            for diff in dep_repo.git.diff("--name-only").splitlines(): # type: ignore
                if diff.endswith(".h"): # type: ignore
                    dep_repo.git.checkout(diff) # type: ignore


        except subprocess.CalledProcessError:
            traceback.print_exc()
            print_err(f"Failed to add '{suffix}' suffix")
            return False

    # Rename the headers last
    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML, "--force", "-i"]

    for file in dep_repo.git.ls_tree("-r", "HEAD", "--name-only").splitlines(): # type: ignore
        if not file.endswith(".h"): # type: ignore
            continue

        if CONFIG.VERBOSITY >= 2:
            print(' '.join(cmd+[file])) # type: ignore
        try:
            (subprocess.run(cmd + [ file ], cwd = dep_path, # type: ignore
            stdout = sys.stdout, stderr = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
            print_err(f"Failed to add '{suffix}' suffix")
            return False


    if CONFIG.VERBOSITY >= 1:
        print_info(f"clang-rename execution time: {datetime.now() - start_time}") # type: ignore

    return True
