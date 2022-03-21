import shutil, subprocess, os, sys, multiprocessing, traceback, re
from git.exc import GitCommandError
from git.objects.commit import Commit
from git.repo.base import Repo

from cparser.util import print_err, print_info
from cparser import CONFIG

def get_bear_version(path: str) -> int:
    if shutil.which("bear") is None:
        print_err("Missing 'bear' executable")
        compile_db_fail_msg(path)
        return -1
    out = subprocess.run([ "bear", "--version" ], capture_output=True, text=True)
    prefix_len = len("bear ")
    return int(out.stdout[prefix_len])

def run_if_present(path:str, filename: str) -> bool:
    if os.path.exists(f"{path}/{filename}"):
        try:
            print_info(f"{path}: Running ./{filename}...")
            (subprocess.run([ f"./{filename}" ], cwd = path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(path)
            return False
    return True

def autogen_compile_db(source_path: str) -> bool:
    cmds_json = f"{source_path}/compile_commands.json"

    if os.path.exists(cmds_json):
        return True

    # 1. Configure the project according to ./configure if applicable
    run_if_present(source_path, "configure")
    run_if_present(source_path, "Configure")

    # 3. Run 'make' with 'bear'
    if os.path.exists(f"{source_path}/Makefile"):
        try:
            print_info(f"Generating {cmds_json}...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1)
            ]
            version = get_bear_version(source_path)

            if version <= 0:
                compile_db_fail_msg(source_path)
                return False
            elif version <= 2:
                del cmd[1]
            (subprocess.run(cmd, cwd = source_path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(source_path)
            return False

    # If the project has already been built the database will be empty
    f = open(cmds_json, mode="r", encoding = "utf8")

    if f.read().startswith("[]"):
        print_err(f"Empty compile_commands.json generated: Clean '{source_path}' and try agian")
        f.close()
        os.remove(cmds_json)
        return False

    return True

def compile_db_fail_msg(path: str) -> None:
    backtrace = traceback.format_exc()
    if not re.match("^NoneType: None$", backtrace):
        print(backtrace)
    print_err(f"Failed to parse or create {path}/compile_commands.json\n" +
    "The compilation database can be manually created using `bear -- <build command>` e.g. `bear -- make`\n" +
    "Consult the documentation for your particular dependency for additional build instructions.")

def create_worktree(target: str, commit: Commit, repo: Repo) -> bool:
    if not os.path.exists(target):
        print_info(f"Creating worktree at {target}")
        # git checkout COMMIT_NEW.hexsha
        # git checkout -b euf-abcdefghi
        # git worktree add -b euf-abcdefghi /tmp/openssl euf-abcdefghi
        try:
            repo.git.worktree("add", "-b", f"euf-{commit.hexsha[:8]}", target, commit.hexsha) # type: ignore
        except GitCommandError:
            traceback.print_exc()
            return False
    return True

def build_goto_lib(dep_dir: str, deplib_name: str, force_recompile: bool) -> str:
    '''
    Returns the path to the built library or an empty string on failure
    '''
    script_env = os.environ.copy()
    script_env.update({
        'DEPENDENCY_DIR': dep_dir,
        'SETX': CONFIG.SETX,
        'FORCE_RECOMPILE': str(force_recompile).lower(),
        'DEPLIB_NAME': deplib_name
    })

    lib_path = ""

    try:
        proc = subprocess.run([ CONFIG.GOTO_BUILD_SCRIPT ],
            env = script_env, stdout = subprocess.PIPE, cwd = dep_dir
        )
        proc.check_returncode()
        lines = proc.stdout.splitlines()

        if lines:
            lib_path = lines[-1].decode('ascii')

    except subprocess.CalledProcessError:
        traceback.print_exc()

    return lib_path

