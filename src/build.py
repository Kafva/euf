import shutil, subprocess, os, sys, multiprocessing, traceback, re, json
from clang import cindex
from git.repo.base import Repo
from src import ERR_EXIT

from src.util import git_dir, print_info, find, print_err
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

def has_non_empty_compile_db(source_dir: str) -> bool:
    '''
    Returns true if a non-empty ccdb without "command" keys is given.
    Note: This does not verify all internal assumptions for the ccdb, 
    these assumptions are asserted to be true (or fixed if false) 
    in `write_canoncial_ccdb`.
    '''
    ccdb_path = f"{source_dir}/compile_commands.json"
    success = False

    if os.path.isfile(ccdb_path):
        # If the project has already been built the database will be empty
        with open(ccdb_path, mode="r", encoding = "utf8") as f:
            ccdb_json = json.load(f)

            if len(ccdb_json) == 0:
                print_err(f"{source_dir}: Empty compile_commands.json found")
                success = False
            elif 'command' in ccdb_json[0]:
                print_err(f"{source_dir}: Invalid compile_commands.json format:"
                           " found 'command' key, expected 'arguments' key"
                )
                success = False
            else:
                success = True

        if not success:
            print_info(f"Removing {ccdb_path}")
            os.remove(ccdb_path)

    return success

def autogen_compile_db(source_dir: str) -> bool:
    script_env = CONFIG.get_script_env()
    ccdb_path = f"{source_dir}/compile_commands.json"

    # Check if a compile_commands.json already exists, if so
    # write it on canonical form to disk
    if has_non_empty_compile_db(source_dir) and not CONFIG.FORCE_CCDB_RECOMPILE:
        return write_canoncial_ccdb(source_dir, ccdb_path)

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

    if os.path.isfile(f"{source_dir}/Makefile"):
        try:
            print_info(f"Generating {ccdb_path}...")
            cmd = [ "bear", "--", "make", "-j",
                    str(multiprocessing.cpu_count() - 1),
            ]
            if version <= 0:
                print_err("Unknown version or non-existent 'bear' executable")
                return False
            if version <= 2:
                del cmd[1]

            if CONFIG.VERBOSITY >= 0:
                print("!> " + ' '.join(cmd))
            (subprocess.run(cmd, cwd = source_dir, stdout = out, stderr = out
            )).check_returncode()
        except subprocess.CalledProcessError:
            check_ccdb_error(source_dir)

    # Read in the ccdb and write it back to disk on a format that adheres
    # with internal assumptions of EUF
    return write_canoncial_ccdb(source_dir, ccdb_path)

def remove_dependency_entries_from_project_db(ccdb_json: list[dict],
 ccdb_path:str) -> list[dict]:
    dep_name = os.path.basename(CONFIG.DEPENDENCY_DIR)
    if CONFIG.VERBOSITY >= 1:
        print_info(f"Removing entries from '{dep_name}' in {ccdb_path}")

    filtered_db = []
    for tu in ccdb_json:
        if re.match(rf".*/{dep_name}/.*", tu['file']) is None:
            filtered_db.append(tu)

    return filtered_db

def assert_abspaths(ccdb_json: list[dict]) -> list[dict]:
    '''
    Ensure that the "output" and "file" keys all specify files using 
    absolute paths. If no "output" field exists, add one based on the
    assumption that the output is given right after the -o flag.
    '''
    for tu in ccdb_json:
        if 'output' not in tu:
            try:
                # Find the [-o] flag and extract the target name after it
                out_idx = tu['arguments'].index("-o")
                out_val = tu['arguments'][out_idx+1]
            except (ValueError,IndexError):
                print_err("Invalid entry in compile_commands.json: "
                         f"'{tu['file']}'"
                )
                sys.exit(ERR_EXIT)
        else:
            out_val = tu['output']

        if not out_val.startswith("/"):
            tu['output'] = tu['directory'] + "/" + out_val

        if not tu['file'].startswith("/"):
            tu['file'] = tu['directory'] + "/" + tu['file']

    return ccdb_json

def write_canoncial_ccdb(source_dir:str, ccdb_path:str) -> bool:
    '''
    Read in the ccdb and write it back on a format that adheres
    with internal assumptions
    '''
    with open(ccdb_path, mode = 'r', encoding='utf8') as f:
        ccdb_json = json.load(f)

    # In bear versions prior to v3, there is no output field so we need to
    # manually insert one...
    ccdb_json = assert_abspaths(ccdb_json)

    # If the project being analyzed builds the dependency from source,
    # e.g. jq and oniguruma, the ccdb for the main project may contain 
    # entries for the dependency. For our use case, we do not want these
    # entries present and therefore remove them
    if source_dir is CONFIG.PROJECT_DIR and os.path.isfile(ccdb_path):
        ccdb_json = remove_dependency_entries_from_project_db(ccdb_json,
                ccdb_path)

    # Include paths and define statements must be given
    #  as a single item "-I", "include" -> "-Iinclude"
    combine_with_next = False

    for tu in ccdb_json:
        for i,_ in enumerate(tu['arguments']):
            if combine_with_next:
                tu['arguments'][i-1] += tu['arguments'][i]
                del tu['arguments'][i]
                combine_with_next = False

            # Check if the argument is -I or -D AFTER any
            # potential combination, otherwise we can skip
            # entries by mistake
            if tu['arguments'][i] in ("-I", "-D"):
                combine_with_next = True

    # Open up each arguments array and find the index of "-o" and "-c".
    # Place these along with the item following "-o" and the source file 
    # last in the array
    for tu in ccdb_json:

        src_file = tu['file'].removeprefix(tu['directory']+"/")

        try:
            o_flag_idx = tu['arguments'].index("-o")
            del tu['arguments'][o_flag_idx]

            # Delete the output file entry
            output_file = tu['arguments'][o_flag_idx]
            del tu['arguments'][o_flag_idx]

            src_idx = tu['arguments'].index(src_file)
            del tu['arguments'][src_idx]

        except ValueError:
            traceback.print_exc()
            return False

        # (-c is optional)
        try:
            c_flag_idx = tu['arguments'].index("-c")
            del tu['arguments'][c_flag_idx]
            tu['arguments'].extend(["-c", "-o", output_file, src_file])
        except ValueError:
            tu['arguments'].extend(["-o", output_file, src_file])

    # Sort the array based on 'output' + 'file' to 
    # ensure that the ccdb always looks the same for a project
    ccdb_json = sorted(ccdb_json, key = lambda entry:
            entry['file'] + (entry['output'] if 'output' in entry else '')
    )

    # Write back the verified version of the ccdb to disk
    with open(ccdb_path, mode='w', encoding='utf8') as f:
        json.dump(ccdb_json, f, ensure_ascii=True, indent=4, sort_keys=True)
        f.write('\n')

    return True

def check_ccdb_error(path: str) -> None:
    ''' Exits the program if the ccdb is empty or does not exist '''
    backtrace = traceback.format_exc()
    if not has_non_empty_compile_db(path):
        if not re.match("^NoneType: None$", backtrace):
            print(backtrace)
        print_err(f"Failed to parse or create {path}/compile_commands.json\n"
        "The compilation database can be manually created using "
        "`bear -- <build command>` e.g. `bear -- make`\n"
        "Consult the documentation for your particular dependency for "
        "additional build instructions.")
        sys.exit(ERR_EXIT)
    else:
        print_err(f"An error occurred but {path}/compile_commands.json "
                "was created")

def create_ccdb(source_dir:str) -> cindex.CompilationDatabase:
    '''
    For the AST to contain a resolved view of the symbols
    we need to provide the correct compile commands
    '''
    if not autogen_compile_db(source_dir):
        sys.exit(ERR_EXIT)

    try:
        ccdb: cindex.CompilationDatabase  = \
            cindex.CompilationDatabase.fromDirectory(source_dir)
    except cindex.CompilationDatabaseError:
        print_err(f"Failed to parse {source_dir}/compile_commands.json")
        sys.exit(ERR_EXIT)
    return ccdb

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

    with subprocess.Popen(["ar", "t", libpath ], cwd = source_dir, env =
      script_env, stdout = subprocess.PIPE, stderr = subprocess.DEVNULL) as p:
        first_binary = p.stdout.readline().decode('ascii').strip('\n') # type: ignore

    with subprocess.Popen(["ar", "p", libpath, first_binary ],
         cwd = source_dir, env = script_env, stdout = subprocess.PIPE) as p:

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

