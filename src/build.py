import shutil, subprocess, os, sys, multiprocessing, traceback, re, json
from clang import cindex
from git.repo.base import Repo
from src import ERR_EXIT

from src.util import git_dir, has_allowed_suffix, print_info, find, print_err
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
        print_err(f"{path}: Missing autoconf files")
        return False

    return True

def has_valid_compile_db(source_dir: str) -> bool:
    ccdb_path = f"{source_dir}/compile_commands.json"

    if os.path.isfile(ccdb_path):
        # If the project has already been built the database will be empty
        success = True
        with open(ccdb_path, mode="r", encoding = "utf8") as f:

            ccdb_json = json.load(f)

            if len(ccdb_json) == 0:
                print_err(f"{source_dir}: Empty compile_commands.json found")
                success = False
            elif 'command' in ccdb_json[0]:
                print_err(f"{source_dir}: Invalid compile_commands.json format: found " + \
                        "'command' key, expected 'arguments' key")
                success = False

        if not success:
            print_info(f"Removing {ccdb_path}")
            os.remove(ccdb_path)

        return success
    else:
        return False

def autogen_compile_db(source_dir: str) -> bool:
    script_env = CONFIG.get_script_env()

    if has_valid_compile_db(source_dir) and not CONFIG.FORCE_CCDB_RECOMPILE:
        return True
    else:
        # If we are creating a compile_commands.json we need to ensure
        # that the project is clean, otherwise nothing will be built
        # and the db will be empty
        # Removing this will cause certain tests to fail
        make_clean(source_dir, script_env, subprocess.DEVNULL)

    out = subprocess.DEVNULL if CONFIG.QUIET_BUILD else sys.stderr

    # For some projects (e.g. older versions of expat), `autoreconf -vfi` 
    # needs to be manually invoked to create configure
    if not os.path.isfile(f"{source_dir}/configure"):
        print_err(f"{source_dir}: Missing ./configure")
        run_autoreconf(source_dir, out)

    conf_script = None
    if os.path.isfile(f"{source_dir}/configure"):
        conf_script = f"{source_dir}/configure"
    elif os.path.isfile(f"{source_dir}/Configure"):
        conf_script = f"{source_dir}/Configure"

    # 1. Configure the project according to ./configure if applicable
    # CC=goto-cc should NOT be set when generating the ccdb since this
    # can cause platform specific definitions to be omitted
    if conf_script:
        script_env.update(CONFIG.BUILD_ENV)
        script_env.update({"CC": CONFIG.CCDB_CC})
        try:
            print_info(f"{source_dir}: Running {conf_script}...")
            (subprocess.run([ conf_script ],
                cwd = source_dir, stdout = out, stderr = out,
                env = script_env
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(source_dir)

    # 3. Run 'make' with 'bear'
    version = get_bear_version(source_dir)
    ccdb_path = f"{source_dir}/compile_commands.json"

    if os.path.isfile(f"{source_dir}/Makefile"):
        try:
            print_info(f"Generating {ccdb_path}...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1),
            ]
            if version <= 0:
                print_err("Unknown version or non-existent 'bear' executable")
                return False
            elif version <= 2:
                del cmd[1]
            print("!> " + ' '.join(cmd))
            (subprocess.run(cmd, cwd = source_dir, stdout = out, stderr = out
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(source_dir)

    # In bear versions prior to v3, there is no output field so we need to
    # manually insert one...
    if version <= 2:
        try:
            patch_old_bear_db(f"{source_dir}/compile_commands.json")
        except:
            print_err(f"Error patching {source_dir}/compile_commands.json")
            sys.exit(ERR_EXIT)

    # 4. If the project being analyzed builds the dependency from source,
    # e.g. jq and oniguruma, the ccdb for the main project may contain 
    # entries for the dependency. For our use case, we do not want these
    # entries present and therefore remove them
    if source_dir == CONFIG.PROJECT_DIR and os.path.isfile(ccdb_path):
        remove_dependency_entries_from_project_db(ccdb_path)

    # 5. Read in the ccdb and write it to disk manually to ensure
    # a sorted order of the entries. We also reorder the arguments
    # array so that it always conforms to the assumotion that the 
    # last four arguments will be
    #  "-c" "-o" "<.o>" "<.c>"
    json_db = {}
    with open(ccdb_path, mode = 'r', encoding='utf8') as f:
        json_db = json.load(f)

    write_ccdb_from_object(ccdb_path, json_db)

    return has_valid_compile_db(source_dir)

def remove_dependency_entries_from_project_db(ccdb_path: str):
    dep_name = os.path.basename(CONFIG.DEPENDENCY_DIR)
    print_info(f"Removing entries from '{dep_name}' in {ccdb_path}")
    with open(ccdb_path, mode="r", encoding = "utf8") as f:
        filtered_db = []
        ccdb_json = json.load(f)
        for tu in ccdb_json:
            if re.match(rf".*/{dep_name}/.*", tu['file']) == None:
                filtered_db.append(tu)

    write_ccdb_from_object(ccdb_path, filtered_db)

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

    # Open up each arguments array and find the index of "-o" and "-c".
    # Place these along with the item following "-o" and the source file 
    # last in the array
    for tu in json_db:
        src_files = list(filter(lambda a: \
                    has_allowed_suffix(a) and \
                    (
                        os.path.isfile(tu['directory']+"/"+a) or
                        os.path.isfile(a)
                    ),
                    tu['arguments']
                ))
        try:
            src_file = src_files[len(src_files)-1]

            o_flag_idx = tu['arguments'].index("-o")
            del tu['arguments'][o_flag_idx]

            # Delete the output file entry
            output_file = tu['arguments'][o_flag_idx]
            del tu['arguments'][o_flag_idx]

            c_flag_idx = tu['arguments'].index("-c")
            del tu['arguments'][c_flag_idx]

            src_idx = tu['arguments'].index(src_file)
            del tu['arguments'][src_idx]
        except (ValueError,IndexError):
            traceback.print_exc()
            print_err(f"Failed to create {ccdb_path}")
            sys.exit(ERR_EXIT)

        tu['arguments'].extend(["-c", "-o", output_file, src_file])

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
        print_err(f"An error occurred but {path}/compile_commands.json was created")

def make_clean(source_dir: str, script_env: dict[str,str], out) -> bool:
    if os.path.isfile(f"{source_dir}/Makefile"):
        try:
            if CONFIG.VERBOSITY >= 1:
                print("!> make clean")
            subprocess.run([ "make", "clean"],
                stdout = out, stderr = out,
                cwd = source_dir, env = script_env
            ).check_returncode()
        except subprocess.CalledProcessError:
            traceback.print_exc()
            return False
    return True

def lib_is_gbf(source_dir: str, libpath: str) -> bool:
    script_env = CONFIG.get_script_env()
    p = subprocess.Popen(["ar", "t", libpath ], cwd = source_dir, env =
            script_env, stdout = subprocess.PIPE, stderr = subprocess.DEVNULL)
    first_binary = p.stdout.readline().decode('ascii').strip('\n') # type: ignore
    p = subprocess.Popen(["ar", "p", libpath, first_binary ], cwd = source_dir, env =
            script_env, stdout = subprocess.PIPE)

    return p.stdout.read(4) == b'\x7fGBF' # type: ignore

def build_goto_lib(source_dir: str, new_version: bool) -> str:
    '''
    Returns the path to the built library or an empty string on failure
    '''
    script_env = CONFIG.get_script_env()
    out = subprocess.DEVNULL if CONFIG.QUIET_BUILD else sys.stderr

    if os.path.isfile(f"{source_dir}/configure") or \
       os.path.isfile(f"{source_dir}/Makefile"):
        # Recompile if the library cannot be found or is on ELF format
        if (libpath := find(CONFIG.DEPLIB_NAME, source_dir)) == "" or \
            not lib_is_gbf(source_dir,libpath) or \
            CONFIG.FORCE_RECOMPILE:

            if CONFIG.VERBOSITY > 0:
                print_info(f"Building GOTO bin library: {source_dir}")

            # 1. Clean the project from ELF binaries
            if not make_clean(source_dir, script_env, out):
                return ""

            # Remove any other extraneous files
            Repo(git_dir(new=new_version)).git.clean( # type: ignore
                "-df", "--exclude=compile_commands.json", \
                f"--exclude={CONFIG.HARNESS_DIR}"
            )

            # 2. Run `./configure` and `make` with goto-cc
            # as the compiler and any other custom flags
            script_env.update({"CC": "goto-cc"})
            script_env.update(CONFIG.BUILD_ENV)

            try:
                if os.path.isfile(f"{source_dir}/configure"):
                    if CONFIG.VERBOSITY >= 1:
                        print("!> ./configure")
                    subprocess.run([
                        "./configure", "--host", "none-none-none"
                        ],
                        stdout = out, stderr = out,
                        cwd = source_dir, env = script_env
                    ).check_returncode()

                if new_version:
                    # Tell CBMC to add a suffix to every global
                    # symbol when we compile the old version
                    script_env.update({CONFIG.SUFFIX_ENV_FLAG: '1'})

                cmd = ["make", "-j", str(multiprocessing.cpu_count() - 1) ]

                if CONFIG.VERBOSITY >= 1:
                    print(f"!> {' '.join(cmd)}")

                subprocess.run(cmd,
                    stdout = out, stderr = out,
                    cwd = source_dir, env = script_env
                ).check_returncode()

            except subprocess.CalledProcessError:
                traceback.print_exc()
                return ""

    return find(CONFIG.DEPLIB_NAME, source_dir)

def create_ccdb(source_dir:str) -> cindex.CompilationDatabase:
    '''
    For the AST to contain a resolved view of the symbols
    we need to provide the correct compile commands
    '''
    if not autogen_compile_db(source_dir): sys.exit(ERR_EXIT)

    try:
        ccdb: cindex.CompilationDatabase  = \
            cindex.CompilationDatabase.fromDirectory(source_dir)
    except cindex.CompilationDatabaseError:
        print_err(f"Failed to parse {source_dir}/compile_commands.json")
        sys.exit(ERR_EXIT)
    return ccdb
