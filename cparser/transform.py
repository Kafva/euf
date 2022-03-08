import subprocess, os, sys, traceback
from clang import cindex
from typing import Set
from git import Repo
from cparser.util import flatten, print_err, print_info, remove_prefix, top_stash_is_euf_internal
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


def clang_rename(filepath: list[str], commands: list[str], cwd: str) -> bool:
    '''
    Replace all files with new versions that have their global symbols renamed
    '''

    # For clang-rename to consistently rename symbols we need to run it agianst
    # all source files at once and not one by one
    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML,
        filepath, "--force", "-i",  "--" ] + commands

    if CONFIG.VERBOSITY >= 2:
        print_info(f"Patching {filepath}\n" + ' '.join(commands))

    try:
        (subprocess.run(cmd, cwd = cwd,
        stdout = subprocess.DEVNULL, stderr = subprocess.DEVNULL
        )).check_returncode()
    except subprocess.CalledProcessError:
        traceback.print_exc()
        print_err(f"Failed to patch {filepath}")
        return False

    return True


def add_suffix_to_globals(dep_path: str, ccdb: cindex.CompilationDatabase,
    suffix: str = "_old") -> bool:
    '''
    Go through every TU in the compilation database
    and save the top level declerations. 

    Then go through every source file and add a suffix
    to every occurence of the global symbols using
    'clang-rename'
    '''

    dep_name = os.path.basename(dep_path)
    dep_repo = Repo(dep_path)

    if top_stash_is_euf_internal(dep_repo):
        print_info(f"Using existing stash to add '{suffix}' to {dep_name}")
        dep_repo.git.stash("pop") # type: ignore
        return True

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

    # For `clang-rename` to consistently rename symbols we need to run it 
    # against all source files at once 
    # This means that we cannot supply compiler directives for specific files
    # FIXME: We currently supply a set of all flags from ccdb applied to
    # all files
    ccmds = list(ccdb.getAllCompileCommands())
    filepaths: list[str]        = list(map(lambda ccmd:
        "." + remove_prefix(ccmd.filename,dep_path), ccmds
    ))
    commands: list[list[str]]   = list(map(lambda ccmd:
        list(ccmd.arguments)[1:-4], ccmds
    ))

    all_cc_commands = set(flatten(commands))

    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML, "--force", "-i" ] + \
            filepaths + [ "--" ] + list(all_cc_commands)

    if CONFIG.VERBOSITY >= 2:
        print(' '.join(cmd))

    try:
        (subprocess.run(cmd, cwd = dep_path,
        stdout = sys.stderr, stderr = sys.stderr
        )).check_returncode()
    except subprocess.CalledProcessError:
        traceback.print_exc()
        print_err(f"Failed to add '{suffix}' suffix")
        return False
    return success
