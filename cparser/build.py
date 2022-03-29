import shutil, subprocess, os, sys, multiprocessing, traceback, re
from git.exc import GitCommandError
from git.objects.commit import Commit
from git.repo.base import Repo

from cparser.util import print_err, print_info, find
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
    script_env = os.environ.copy()

    if filename.lower() == "configure":
        script_env.update(CONFIG.BUILD_ENV)

    if os.path.exists(f"{path}/{filename}"):
        try:
            print_info(f"{path}: Running ./{filename}...")
            (subprocess.run([ f"./{filename}", ],
                cwd = path, stdout = sys.stderr,
                env = script_env
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(path)
            return False
    return True


def has_valid_compile_db(source_path: str) -> bool:
    cmds_json = f"{source_path}/compile_commands.json"

    if os.path.exists(cmds_json):
        # If the project has already been built the database will be empty
        f = open(cmds_json, mode="r", encoding = "utf8")

        if f.read().startswith("[]"):
            print_err(f"Empty compile_commands.json found at '{source_path}'")
            f.close()
            os.remove(cmds_json)
            return False

        return True
    else:
        return False


def autogen_compile_db(source_path: str) -> bool:

    if has_valid_compile_db(source_path):
        return True

    # 1. Configure the project according to ./configure if applicable
    run_if_present(source_path, "configure")
    run_if_present(source_path, "Configure")

    # 3. Run 'make' with 'bear'
    if os.path.exists(f"{source_path}/Makefile"):
        try:
            print_info(f"Generating {source_path}/compile_commands.json...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1),
            ]
            version = get_bear_version(source_path)

            if version <= 0:
                compile_db_fail_msg(source_path)
                return False
            elif version <= 2:
                del cmd[1]

            print(cmd)
            (subprocess.run(cmd, cwd = source_path, stdout = sys.stderr
            )).check_returncode()
        except subprocess.CalledProcessError:
            compile_db_fail_msg(source_path)
            return False

    return has_valid_compile_db(source_path)

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

def dir_has_magic_file(dep_source_dir: str, magic: bytes = b'\x7fELF') -> bool:
    has_elf = False
    for root, _, filenames in os.walk(dep_source_dir):
        for filename in filenames:
            with open(f"{root}/{filename}", mode="rb") as f:
                if f.read(4) == magic:
                    has_elf = True
                    break
    return has_elf

def build_goto_lib(dep_source_dir: str, dep_dir: str) -> str:
    '''
    Returns the path to the built library or an empty string on failure
    '''
    script_env = CONFIG.get_script_env()
    if CONFIG.VERBOSITY >= 0:
        out = sys.stderr
    else:
        out = subprocess.DEVNULL

    if CONFIG.GOTO_BUILD_SCRIPT != "":
        script_env.update({
            'DEP_DIR_EUF': dep_source_dir,
            'FORCE_RECOMPILE': str(CONFIG.FORCE_RECOMPILE).lower(),
        })
        try:
            subprocess.run([ CONFIG.GOTO_BUILD_SCRIPT ],
                stdout = out, stderr = out,
                cwd = dep_dir, env = script_env
            ).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
    elif os.path.exists(f"{dep_source_dir}/configure"):
        # Always recompile if at least one file in the project is 
        # an ELF binary, goto-bin files are recorded as 'data' with `file`
        if dir_has_magic_file(dep_source_dir) or CONFIG.FORCE_RECOMPILE or \
            not find(CONFIG.DEPLIB_NAME, dep_dir):
            # 1. Clean the project from ELF binaries
            try:
                subprocess.run([ "make", "clean"],
                    stdout = out, stderr = out,
                    cwd = dep_source_dir, env = script_env
                ).check_returncode()
            except subprocess.CalledProcessError:
                traceback.print_exc()
                return ""

            # Remove any other extranous files
            Repo(dep_dir).git.clean( # type: ignore
                "-df", "--exclude=compile_commands.json"
            )

            # 2. Run `./configure` and `make` with goto-cc
            # as the compiler and any other custom flags
            script_env.update({"CC": "goto-cc"})
            script_env.update(CONFIG.BUILD_ENV)

            try:
                subprocess.run([
                    "./configure", "--host", "none-none-none"
                    ],
                    stdout = out, stderr = out,
                    cwd = dep_source_dir, env = script_env
                ).check_returncode()

                subprocess.run([
                    "make", "-j",
                    str(multiprocessing.cpu_count() - 1)
                    ],
                    stdout = out, stderr = out,
                    cwd = dep_source_dir, env = script_env
                ).check_returncode()
            except subprocess.CalledProcessError:
                traceback.print_exc()
                return ""

    return find(CONFIG.DEPLIB_NAME, dep_dir)

