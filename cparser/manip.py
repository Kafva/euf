import shutil, subprocess, os, sys, multiprocessing, traceback, re
from clang import cindex
from typing import Set
from git.objects.commit import Commit

from cparser.change_set import get_top_level_decls
from cparser.util import print_err, print_info, done
from cparser import CONFIG

def get_bear_version(path: str) -> int:
    if shutil.which("bear") is None:
        print_err("Missing 'bear' executable")
        compile_db_fail_msg(path)
    out = subprocess.run([ "bear", "--version" ], capture_output=True, text=True)
    prefix_len = len("bear ")
    return int(out.stdout[prefix_len])

def run_if_present(path:str, filename: str):
    if os.path.exists(f"{path}/{filename}"):
        try:
            print_info(f"{path}: Running ./{filename}...")
            (subprocess.run([ f"./{filename}" ], cwd = path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(path)


def autogen_compile_db(path: str):
    if os.path.exists(f"{path}/compile_commands.json"):
        return

    # 1. Configure the project according to ./configure.ac if applicable
    if os.path.exists(f"{path}/configure.ac"):
        try:
            print_info(f"{path}: Running autoreconf...")
            (subprocess.run([ "autoreconf", "-vfi" ],
                cwd = path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(path)

    # 2. Configure the project according to ./configure if applicable
    run_if_present(path, "configure")
    run_if_present(path, "Configure")

    # 3. Run 'make' with 'bear'
    if os.path.exists(f"{path}/Makefile"):
        try:
            print_info(f"Generating {path}/compile_commands.json...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1)
            ]
            if get_bear_version(path) <= 2:
                del cmd[1]
            (subprocess.run(cmd, cwd = path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(path)

def compile_db_fail_msg(path: str):
    backtrace = traceback.format_exc()
    if not re.match("^NoneType: None$", backtrace):
        print(backtrace)
    print_err(f"Failed to parse {path}/compile_commands.json\n" +
    "The compilation database can be created using `bear -- <build command>` e.g. `bear -- make`\n" +
    "Consult the documentation for your particular dependency for additional build instructions.")
    done(1)

def create_worktree(target: str, cwd: str, commit: Commit):
    if not os.path.exists(target):
        print_info(f"Creating worktree at {target}")
        try:
           # git checkout COMMIT_NEW.hexsha
           # git checkout -b euf-abcdefghi
           # git worktree add -b euf-abcdefghi /tmp/openssl euf-abcdefghi
            (subprocess.run([
                    "git", "worktree", "add", "-b",
                    f"euf-{commit.hexsha[:8]}",
                    target, commit.hexsha
                ],
                cwd = cwd, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            print(traceback.format_exc())
            done(1)

def add_suffix_to_globals(path: str, ccdb: cindex.CompilationDatabase, suffix: str = "_old"):
    '''
    Go through every TU in the compilation database
    and save the top level declerations. 

    Then go through every source file and add a suffix
    to every occurence of the global symbols using
    'clang-rename'
    '''
    dep_name = os.path.basename(path)
    lock_file = f"{CONFIG.EUF_CACHE}/{dep_name}.lock"

    if os.path.exists(lock_file):
        return

    print_info(f"Adding '{suffix}' suffixes to {dep_name}...")

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
            done(1)

        global_names |= get_top_level_decls(cursor, path)


    # Generate a Qualified -> NewName YAML file with translations for all of the
    # identified symbols
    with open(CONFIG.RENAME_YML, "w", encoding="utf8") as f:
        f.write("---\n")
        for name in global_names:
            f.write(f"- QualifiedName: {name}\n  NewName: {name}{suffix}\n")


    # Replace all files with new versions that have the global symbols renamed
    for ccmds in ccdb.getAllCompileCommands():
        if ccmds.filename != "/home/jonas/Repos/oniguruma/regexec.c":
            continue
        print_err(ccmds.filename)
        try:
            cmd = [ "clang-rename", "--input", CONFIG.RENAME_YML,
                ccmds.filename, "--force",  "--" ] + \
                list(ccmds.arguments)[1:-1]
            print(' '.join(cmd))

            (subprocess.run(cmd, cwd = path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            traceback.format_exc()
            print_err(f"Failed to add suffixes to: {ccmds.filename}")
            done(1)


    # Add a '.lockfile' to indicate that the path has been manipulated
    # by `clang-rename`
    open(lock_file, 'w', encoding="utf8").close()

