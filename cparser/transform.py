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


def clang_rename(filepath: str, commands: list[str], cwd: str) -> bool:
    '''
    Replace all files with new versions that have their global symbols renamed
    clang-rename --input /tmp/rename.yml /home/jonas/.cache/euf/oniguruma-65a9b1aa/regcomp.c -pn --force -i -- -DHAVE_CONFIG_H -I. -I. -I/usr/local/include -g -O2 -c -fPIC
    '''
    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML,
        filepath, "--force", "-i",  "--" ] + commands

    if CONFIG.VERBOSITY >= 2:
        print_info(f"Patching {filepath}\n" + ' '.join(commands))

    try:
        (subprocess.run(cmd, cwd = cwd, stdout = sys.stderr
        )).check_returncode()
    except subprocess.CalledProcessError:
        traceback.print_exc()
        print_err(f"Failed to patch {filepath}")
        return False

    return True


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

    success = True

    # The renaming process has to be sequential since each invocation
    # of `clang-rename` can affect several files
    #
    # Running `clang-rename` with the same words repeatedly seems to cause issues...
    for ccmd in ccdb.getAllCompileCommands():
        if dep_only_path != "" and dep_only_path != ccmd.filename:
            continue
        # The first 'cc' and last three arguments '-c' '-o' 'outfile.o' <source>
        # should be removed when running clang-rename
        if not clang_rename(ccmd.filename, list(ccmd.arguments)[1:-4], dep_path):
            success = False
            break

    # Add a '.lockfile' to indicate that the path has been manipulated
    # by `clang-rename`
    if success:
        open(lock_file, 'w', encoding="utf8").close()

    return success

