import shutil, subprocess, os, sys, multiprocessing, traceback, re
from git.objects.commit import Commit

from cparser.util import print_err, print_info, done

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


