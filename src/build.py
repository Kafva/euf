import shutil, subprocess, os, sys, multiprocessing, traceback, re, json
from clang import cindex
from git.repo.base import Repo
from src import ERR_EXIT

from src.util import print_info, find, print_err
from src.config import CONFIG

def get_bear_version(path: str) -> int:
    if shutil.which("bear") is None:
        print_err("Missing 'bear' executable")
        check_ccdb_error(path)
        return -1
    out = subprocess.run([ "bear", "--version" ], capture_output=True, text=True)
    prefix_len = len("bear ")
    return int(out.stdout[prefix_len])

def run_autoreconf(path: str, out) -> bool:
    script_env = os.environ.copy()

    if os.path.isfile(f"{path}/configure.ac") or \
       os.path.isfile(f"{path}/configure.in"):
        try:
            print_info(f"{path}: Running autoreconf -vfi...")
            (subprocess.run([ "autoreconf", "-vfi" ],
                cwd = path, stdout = out, stderr = out,
                env = script_env
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(path)
    else:
        print_err(f"({path}): Missing autoconf files")
        return False

    return True

def has_valid_compile_db(source_path: str) -> bool:
    cmds_json = f"{source_path}/compile_commands.json"

    if os.path.isfile(cmds_json):
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
    script_env = CONFIG.get_script_env()

    if has_valid_compile_db(source_path) and not CONFIG.FORCE_CCDB_RECOMPILE:
        return True
    else:
        # If we are creating a compile_commands.json we need to ensure
        # that the project is clean, otherwise nothing will be built
        # and the db will be empty
        # Removing this will cause certain tests to fail
        make_clean(source_path, script_env, subprocess.DEVNULL)

    out = subprocess.DEVNULL if CONFIG.QUIET_BUILD else sys.stderr

    # For some projects (e.g. older versions of expat), `autoreconf -vfi` 
    # needs to be manually invoked to create configure
    if not os.path.isfile(f"{source_path}/configure"):
        print_err(f"({source_path}): Missing ./configure")
        run_autoreconf(source_path, out)

    conf_script = None
    if os.path.isfile(f"{source_path}/configure"):
        conf_script = f"{source_path}/configure"
    elif os.path.isfile(f"{source_path}/Configure"):
        conf_script = f"{source_path}/Configure"

    # 1. Configure the project according to ./configure if applicable
    # CC=goto-cc should NOT be set when generating the ccdb since this
    # can cause platform specific definitions to be omitted
    if conf_script:
        script_env.update(CONFIG.BUILD_ENV)
        script_env.update({"CC": CONFIG.CCDB_CC})
        try:
            print_info(f"{source_path}: Running {conf_script}...")
            (subprocess.run([ conf_script ],
                cwd = source_path, stdout = out, stderr = out,
                env = script_env
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(source_path)

    # 3. Run 'make' with 'bear'
    version = get_bear_version(source_path)

    if os.path.isfile(f"{source_path}/Makefile"):
        try:
            print_info(f"Generating {source_path}/compile_commands.json...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1),
            ]
            if version <= 0:
                print_err("Unknown version or non-existent 'bear' executable")
                return False
            elif version <= 2:
                del cmd[1]
            print("!> " + ' '.join(cmd))
            (subprocess.run(cmd, cwd = source_path, stdout = out, stderr = out
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(source_path)

    # In bear versions prior to v3, there is no output field so we need to
    # manaully insert one...
    if version <= 2:
        try:
            patch_old_bear_db(f"{source_path}/compile_commands.json")
        except:
            print_err(f"Error patching {source_path}/compile_commands.json")
            sys.exit(ERR_EXIT)

    # 4. Run 'compdb' to insert entries for '.h' files into the database
    patch_ccdb_with_headers(source_path)

    return has_valid_compile_db(source_path)

def patch_old_bear_db(ccdb_path:str):
    new_json = []
    with open(ccdb_path, mode='r') as f:
        ccdb_json = json.load(f)
        for tu in ccdb_json:
            # Find the [-o] flag and extract the target name after it
            out_idx = tu['arguments'].index("-o")
            tu['output'] = tu['directory'] + f"/{tu['arguments'][out_idx+1]}"
            # Also, insert the full directory path in the file field
            # if it is not already an absolute path
            if not tu['file'].startswith("/"):
                tu['file'] = tu['directory'] + "/" + tu['file']

            new_json.append(tu)

    write_ccdb_from_object(ccdb_path, ccdb_json)

def patch_ccdb_with_headers(source_path: str) -> bool:
    '''
    For some reason... compdb uses a single command string instead of the
    standard arguments array, we need to convert this to maintain
    compatibility with the rest of EUF
    '''
    ccdb_path = f"{source_path}/compile_commands.json"

    if CONFIG.VERBOSITY >= 1:
        print_info("Running compdb...")
    try:
        p = subprocess.Popen(["compdb", "-p", ".", "list"],
            stdout = subprocess.PIPE, stderr = subprocess.DEVNULL,
            cwd = source_path
        )
        json_output = json.load(p.stdout) # type: ignore
        header_entries = []

        for json_entry in json_output:
            if json_entry['file'].endswith(".h"):
                json_entry["arguments"] = json_entry['command'].split(' ')
                del json_entry['command']
                header_entries.append(json_entry)
    except:
        print_err("Failed to patch ccdb with compdb")
        return False

    current_db = []
    with open(ccdb_path, mode='r', encoding='utf8') as f:
        current_db = json.load(f)
        current_db.extend(header_entries)

    write_ccdb_from_object(ccdb_path, current_db)

    return True

def write_ccdb_from_object(ccdb_path:str, json_db: list[dict]):
    '''
    To allow for easy testing, we sort the array based on 
    'output' + 'file',
    ensuring that the ccdb always looks the same for a project 
    (compdb headers do not have an output, which would
    otherwise be a unique field)
    '''
    json_db = sorted(json_db, key = lambda entry:
            entry['file'] + (entry['output'] if 'output' in entry else '')
    )

    with open(ccdb_path, mode='w', encoding='utf8') as f:
        json.dump(json_db, f, ensure_ascii=True, indent=4, sort_keys=True)
        f.write('\n')

def check_ccdb_error(path: str) -> None:
    ''' Exits the program if the ccdb is empty or does not exist '''
    backtrace = traceback.format_exc()
    if not has_valid_compile_db(path):
        if not re.match("^NoneType: None$", backtrace):
            print(backtrace)
        print_err(f"Failed to parse or create {path}/compile_commands.json\n" +
        "The compilation database can be manually created using `bear -- <build command>` e.g. `bear -- make`\n" +
        "Consult the documentation for your particular dependency for additional build instructions.")
        sys.exit(ERR_EXIT)
    else:
        print_err(f"An error occured but {path}/compile_commands.json was created")

def make_clean(dep_source_dir: str, script_env: dict[str,str], out) -> bool:
    if os.path.isfile(f"{dep_source_dir}/Makefile"):
        try:
            if CONFIG.VERBOSITY >= 1:
                print("!> make clean")
            subprocess.run([ "make", "clean"],
                stdout = out, stderr = out,
                cwd = dep_source_dir, env = script_env
            ).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
            return False
    return True

def lib_is_gbf(dep_source_dir: str, libpath: str) -> bool:
    script_env = CONFIG.get_script_env()
    p = subprocess.Popen(["ar", "t", libpath ], cwd = dep_source_dir, env =
            script_env, stdout = subprocess.PIPE, stderr = subprocess.DEVNULL)
    first_binary = p.stdout.readline().decode('ascii').strip('\n') # type: ignore
    p = subprocess.Popen(["ar", "p", libpath, first_binary ], cwd = dep_source_dir, env =
            script_env, stdout = subprocess.PIPE)

    return p.stdout.read(4) == b'\x7fGBF' # type: ignore

def build_goto_lib(dep_source_dir: str, dep_dir: str, old_version: bool) -> str:
    '''
    Returns the path to the built library or an empty string on failure
    '''
    script_env = CONFIG.get_script_env()
    out = subprocess.DEVNULL if CONFIG.QUIET_BUILD else sys.stderr

    if os.path.isfile(f"{dep_source_dir}/configure") or \
       os.path.isfile(f"{dep_source_dir}/Makefile"):
        # Recompile if the library cannot be found or is on ELF format
        if (libpath := find(CONFIG.DEPLIB_NAME, dep_dir)) == "" or \
            not lib_is_gbf(dep_source_dir,libpath) or \
            CONFIG.FORCE_RECOMPILE:

            if CONFIG.VERBOSITY > 0:
                print_info(f"Building GOTO bin library: {dep_dir}")

            # 1. Clean the project from ELF binaries
            if not make_clean(dep_source_dir, script_env, out):
                return ""

            # Remove any other extranous files
            Repo(dep_dir).git.clean( # type: ignore
                "-df", "--exclude=compile_commands.json", \
                f"--exclude={CONFIG.HARNESS_DIR}"
            )

            # 2. Run `./configure` and `make` with goto-cc
            # as the compiler and any other custom flags
            script_env.update({"CC": "goto-cc"})
            script_env.update(CONFIG.BUILD_ENV)

            try:
                if os.path.isfile(f"{dep_source_dir}/configure"):
                    if CONFIG.VERBOSITY >= 1:
                        print("!> ./configure")
                    subprocess.run([
                        "./configure", "--host", "none-none-none"
                        ],
                        stdout = out, stderr = out,
                        cwd = dep_source_dir, env = script_env
                    ).check_returncode()

                if old_version:
                    # Tell CBMC to add a suffix to every global
                    # symbol when we compile the old version
                    script_env.update({CONFIG.SUFFIX_ENV_FLAG: '1'})

                cmd = ["make", "-j", str(multiprocessing.cpu_count() - 1) ]

                if CONFIG.VERBOSITY >= 1:
                    print(f"!> {' '.join(cmd)}")

                subprocess.run(cmd,
                    stdout = out, stderr = out,
                    cwd = dep_source_dir, env = script_env
                ).check_returncode()

            except subprocess.CalledProcessError:
                traceback.print_exc()
                return ""

    return find(CONFIG.DEPLIB_NAME, dep_dir)

def create_ccdb(source_path:str) -> cindex.CompilationDatabase:
    '''
    For the AST to contain a resolved view of the symbols
    we need to provide the correct compile commands
    '''
    if not autogen_compile_db(source_path): sys.exit(ERR_EXIT)

    try:
        ccdb: cindex.CompilationDatabase  = \
            cindex.CompilationDatabase.fromDirectory(source_path)
    except cindex.CompilationDatabaseError:
        print_err(f"Failed to parse {source_path}/compile_commands.json")
        sys.exit(ERR_EXIT)
    return ccdb
