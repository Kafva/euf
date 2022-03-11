import subprocess, os, sys, traceback
from clang import cindex
from typing import Set
from git.repo import Repo
from cparser.util import flatten, print_err, print_info, remove_prefix, \
        unique_only
from cparser import CONFIG, SourceDiff

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

def get_clang_rename_args(basepath: str, ccdb: cindex.CompilationDatabase,
        dep_source_diffs: list[SourceDiff], dep_only_path_old: str) -> tuple[Set[str], list[str], list[str]]:
    '''
    Reads the compilation database and creates:
        1. A set of all top level labels in the changed files that we need to
        rename with a suffix
        2. A list of compile commands to pass to `clang-rename`
        3. A list of the filepaths we should rename with `clang-rename`
    '''
    os.chdir(basepath)

    global_names: Set[str] = set()
    commands: list[str] = []
    filepaths: list[str] = []

    #for ccmds in ccdb.getAllCompileCommands():

    for diff in dep_source_diffs:

        if dep_only_path_old != "" and \
            not diff.old_path.endswith(dep_only_path_old):
            continue

        try:
            # Depending on how the compile_commands.json is read
            # the full path may or may not be present...
            ccmds = ccdb.getCompileCommands(diff.old_path)
            filepath = ccmds[0].filename

            if not filepath.startswith(basepath):
                filepath = basepath + "/" + filepath

            filepaths.append(filepath)

            # For clang-rename we skip: -c -o <.o> <src>
            commands.extend( list(ccmds[0].arguments)[1:-4] )

            try:
                # Exclude 'cc' [0] and source file [-1] from compile command
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = list(ccmds[0].arguments)[1:-1]
                )
                cursor: cindex.Cursor = tu.cursor
                global_names |= get_top_level_decls(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

        except cindex.CompilationDatabaseError:
            traceback.format_exc()
            print_err(f"Failed to get compile commands {diff.old_path}")


    # FIXME: We currently supply a set of all flags from ccdb applied to all files
    return (global_names, unique_only(commands), filepaths)

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
        dep_source_diffs: list[SourceDiff], dep_only_path_old: str, suffix: str = "_old") -> bool:
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

    global_names, commands, filepaths = get_clang_rename_args(dep_path, ccdb,
            dep_source_diffs, dep_only_path_old
    )

    if len(global_names) == 0:
        print_err("No suffixes added")
        return False

    # Generate a Qualified -> NewName YAML file with translations for all of the
    # identified symbols
    with open(CONFIG.RENAME_YML, "w", encoding="utf8") as f:
        f.write("---\n")
        for name in list(global_names):
            f.write(f"- QualifiedName: {name}\n  NewName: {name}{suffix}\n")

    # For clang-rename to consistently rename symbols we need to run it agianst
    # all source files at once and not one by one
    cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML, "--force", "-i" ] + \
            filepaths + [ "--" ] + commands

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

    return True
