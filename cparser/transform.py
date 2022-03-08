from functools import partial
import multiprocessing
import subprocess, os, sys, traceback
from clang import cindex
from typing import Set

from cparser.util import print_err, print_info
from cparser import CONFIG

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_top_level_decls(cursor: cindex.Cursor, basepath: str) -> Set[str]:
    ''' 
    Extract the names of all top level declerations (variables and functions) 
    within the given basepath. Without filtering on the basepath 
    externally defined symbols can appear
    '''
    global_decls: Set[str] = set()

    for child in cursor.get_children():
        if (str(child.kind).endswith("FUNCTION_DECL") or \
            str(child.kind).endswith("VAR_DECL") ) and \
            child.is_definition() and \
            str(child.location.file).startswith(basepath):
                global_decls.add(child.spelling)

    return global_decls

def get_all_top_level_decls(path: str, ccdb: cindex.CompilationDatabase) -> Set[str] | None:
    os.chdir(path)

    global_names: Set[str] = set()

    for ccmds in ccdb.getAllCompileCommands():
        try:
            # Exclude 'cc' [0] and source file [-1] from compile command
            tu = cindex.TranslationUnit.from_source(
                    ccmds.filename,
                    args = list(ccmds.arguments)[1:-1]
            )
            cursor: cindex.Cursor = tu.cursor
        except cindex.TranslationUnitLoadError:
            traceback.format_exc()
            print_err(f"Failed to parse: {ccmds.filename}")
            return

        global_names |= get_top_level_decls(cursor, path)

    return global_names


def clang_rename(filepath: str, commands: list[str], cwd: str) -> None:
    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML,
        filepath, "--force", "-i",  "--" ] + commands

    if CONFIG.VERBOSITY >= 2:
        print_info(f"Patching {filepath}\n" + ' '.join(commands))

    (subprocess.run(cmd, cwd = cwd, stdout = sys.stderr
    )).check_returncode()

def add_suffix_to_globals(dep_path: str, ccdb: cindex.CompilationDatabase,
        dep_only_path: str, suffix: str = "_old") -> bool:
    '''
    Go through every TU in the compilation database
    and save the top level declerations. 

    Then go through every source file and add a suffix
    to every occurence of the global symbols using
    'clang-rename'
    '''
    dep_name = os.path.basename(dep_path)
    lock_file = f"{CONFIG.EUF_CACHE}/{dep_name}.lock"

    if os.path.exists(lock_file):
        return False

    print_info(f"Adding '{suffix}' suffixes to {dep_name}...")

    global_names = get_all_top_level_decls(dep_path, ccdb) # type: ignore
    if not global_names: return False

    # Generate a Qualified -> NewName YAML file with translations for all of the
    # identified symbols
    with open(CONFIG.RENAME_YML, "w", encoding="utf8") as f:
        f.write("---\n")
        for name in global_names:
            f.write(f"- QualifiedName: {name}\n  NewName: {name}{suffix}\n")


    # Replace all files with new versions that have the global symbols renamed
    # We extract the first 'cc' and last three arguments from the ccmds
    #   '-c' '-o' 'outfile.o' <source>
    ccmds = list(ccdb.getAllCompileCommands())
    filepaths: list[str] = list(map(lambda ccmd: ccmd.filename, ccmds))
    commands: list[list[str]] =  list(map(lambda ccmd:
        list(ccmd.arguments)[1:-4], ccmds))

    # Only process a specific file
    if dep_only_path != "":
        try:
            idx = filepaths.index( f"{dep_path}/{dep_only_path}")
        except ValueError:
            print_err(f"Could not find {dep_path}/{dep_only_path}")
            return False
        filepaths = [ filepaths[idx] ]
        commands =  [ commands[idx]  ]

    # TODO: This might haft to be sequential since each process could
    # be manipulating the same files...
    with multiprocessing.Pool(CONFIG.NPROC) as p:
        try:
            p.starmap(partial(clang_rename, cwd = dep_path),
                zip(filepaths, commands)
            )
        except Exception:
            traceback.print_exc()
            return False


    # Add a '.lockfile' to indicate that the path has been manipulated
    # by `clang-rename`
    open(lock_file, 'w', encoding="utf8").close()

    return True

