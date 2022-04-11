from datetime import datetime
import os, subprocess, sys, signal
import shutil

from clang import cindex
from cparser import BASE_DIR, CONFIG, AnalysisResult, DependencyFunction, \
        DependencyFunctionChange, SourceDiff, SourceFile
from cparser.util import print_err, time_end, time_start, wait_on_cr

def get_state_space(changed_functions: list[DependencyFunctionChange], \
        dep_root_dir: str, source_file: SourceFile):
    '''
    To allow for assumptions during the harness generation with CBMC
    we record what values each paramter to a function can take in the
    original program versions and the main project

    The libclang bindings are somewhat less consistent than a real clang plugin for this
    task.
    '''
    translation_unit: cindex.TranslationUnit  = \
            cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.new_compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    get_state_space_from_cursor(dep_root_dir, cursor, changed_functions)

def get_state_space_from_cursor(dep_root_dir: str, cursor: cindex.Cursor,
    changed_functions: list[DependencyFunctionChange]) -> None:
    '''
    Look for calls to functions in the change-set and record what values the parameters
    it is given have.
    '''
    if str(cursor.kind).endswith("CALL_EXPR") and \
        (_ := next(filter(lambda fn: \
        fn.new.ident.spelling == cursor.spelling, changed_functions), None \
    )):
        called = DependencyFunction.new_from_cursor(dep_root_dir, cursor)
        print("=>", called.ident.spelling, called.arguments )

    for child in cursor.get_children():
        get_state_space_from_cursor(dep_root_dir, child, changed_functions)

def add_includes_from_tu(diff: SourceDiff, old_root_dir: str,
        tu_includes: dict[str,tuple[list[str],list[str]]]) -> None:
    '''
    Return a set of all the headers that are included into the TU 
    that corresponds to the given diff split into headers under /usr/inlcude
    and project specific headers.
    The usr headers will be included with <...> in drivers and the others
    will be included using "...", these files will be autaomtaically copied into the
    OUTDIR directory which is on the include path of the driver

    Note that the order of includes matter so we want to use a list

    libexpat has certain "_impl" source files which are included by other files
    and lack any include statements of their own.

    We give the _impl files the same includes as the first file that
    included them (provided that they lack includes of their own)
    '''
    tu_old = cindex.TranslationUnit.from_source(
            f"{old_root_dir}/{diff.old_path}",
            args = diff.old_compile_args
    )
    usr_includes = []
    project_includes = []
    included_c_files = []

    for inc in tu_old.get_includes():
        hdr_path = inc.include.name

        # Record if any .c files are included
        if hdr_path.endswith(".c"):
            trimmed = hdr_path.removeprefix(old_root_dir).strip('/')
            included_c_files.append(trimmed)
            continue

        if hdr_path.startswith("/usr/include/"):
            # Skip system headers under certain specified paths
            if any([ hdr_path.startswith(f"/usr/include/{skip_header}") \
                    for skip_header in CONFIG.SKIP_HEADERS_UNDER ]):
                continue

            if not hdr_path in usr_includes:
                usr_includes.append(
                    hdr_path.removeprefix("/usr/include/")
                )
        else:
            shutil.copy(hdr_path,
                    f"{CONFIG.OUTDIR}/{os.path.basename(hdr_path)}"
                )
            hdr_path = hdr_path.removeprefix(old_root_dir+"/")
            for include_path in CONFIG.DEP_INCLUDE_PATHS:
                hdr_path = hdr_path.strip("/").removeprefix(include_path) \
                    .strip("/")

                if os.path.basename(hdr_path) in CONFIG.BLACKLISTED_HEADERS:
                    continue

                if not hdr_path in project_includes:
                    project_includes.append(hdr_path)

    # Add all of the headers from the current TU to the C files
    # that it includes
    for c_file in included_c_files:
        tu_includes[c_file]    = (usr_includes, project_includes)

    if len(usr_includes) > 0 or len(project_includes) > 0:
        tu_includes[diff.old_path] = (usr_includes, project_includes)

def create_harness(change: DependencyFunctionChange, harness_path: str,
        includes: tuple[list[str],list[str]],  identity: bool = False) -> bool:
    '''
    Firstly, we need to know basic information about the function we are
    generating a harness for:
        full prototype string (forward decl)
        name
        args
        return type
    All of this information has been saved in the `change` object during
    the AST diffing stage.

    "a/" side --> OLD
    "b/" side --> NEW

    If "identity" is set, the comparsion will be made with the old version
    and itself, creating a seperate harness file with the suffix _id
    '''

    # ~~Basic assumptions for harness generation~~
    # The number-of arugments and their types have not changed

    if not identity:
        if (old_cnt := len(change.old.arguments)) != \
            (new_cnt := len(change.new.arguments)):
            print_err(f"Differing number of arguments: a/{old_cnt} -> b/{new_cnt}")
            return False

        for a1,a2 in zip(change.old.arguments,change.new.arguments):
            if a1!=a2:
                print_err(f"Different argument types: a/{a1} -> b/{a2}")
                return False

        # The return-type has not changed
        if change.old.ident != change.new.ident:
            print_err(
                f"Different return type: a/{change.old.ident.type_spelling} " + \
                f"-> b/{change.old.ident.type_spelling}"
            )
            return False

    INDENT=CONFIG.INDENT
    failed_generation = False
    fail_msg = ""

    # Write the harness
    with open(harness_path, mode='w', encoding='utf8') as f:
        # Debug information
        f.write(f"// {change}\n")

        # ifdef to prevent linting warnings
        f.write("#ifdef CBMC\n")

        # System include directives
        for header in includes[0]:
            f.write(f"#include <{header}>\n")

        f.write("\n")

        # Project include directives
        for header in includes[1]:
            f.write(f"#include \"{os.path.basename(header)}\"\n")

        # Any custom include directives for the specific file
        filename = os.path.basename(change.old.filepath)
        if filename in CONFIG.CUSTOM_HEADERS:
            f.write("\n")
            for header in CONFIG.CUSTOM_HEADERS[filename]:
                header = os.path.expanduser(header)
                header_name = os.path.basename(header)
                shutil.copy(header, f"{CONFIG.OUTDIR}/{header_name}")
                f.write(f"#include \"{header_name}\"")
            f.write("\n")


        # Decleration of the old version of the function
        f.write(f"\n{change.old.prototype_string(CONFIG.SUFFIX)};\n")

        if not identity:
            # Decleration for the new version of the function
            #
            # In some cases the function will already be declared in of the headers
            # but providing a second decleration in the driver does
            # not cause issues
            #
            # NOTE: if the function is declared as 'static' in one of the included
            # headers we will not be able to access it a warning akin to
            #
            # **** WARNING: no body for function <...>
            #
            # will show up during the cbmc analysis if this occurs
            f.write(f"{change.new.prototype_string()};\n")

        f.write("\n")

        # Entrypoint function
        f.write(f"void {CONFIG.EUF_ENTRYPOINT}() {{\n")

        # Contracts:
        #   https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/contracts-history-variables.md
        #   https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/contracts-assigns.md
        # Using function constracts abstracts away the actual function body and reduces
        # the search space to the 'ensures' clause of the contract.

        # ~~ Harness components ~~
        #   https://github.com/model-checking/cbmc-starter-kit/wiki/Frequently-Asked-Questions
        #
        # We are not bound to the `nondet_` symbols defined by CBMC internally, any function prefixed
        # with nondet_ is treated as a special case by CBMC and we can thus create our own versions
        # just by writing a prototype string for them with the return type we desire
        #  http://www.cprover.org/cprover-manual/modeling/nondeterminism/ 
        #   
        # 1. Initialization
        # The initialisation involves creating valid, unconstrained and equal
        # data structures that can be passed to the two versions

        # The initialisation procedure is done per function argument and the
        # type of argument dictates how the initialization is done
        arg_string = ""

        if change.old.ident.type_spelling == "void":
            failed_generation = "True"
            fail_msg = f"Cannot verify function with a 'void' return value: {change.old}"
        else:
            for arg in change.old.arguments:
                if not arg.is_ptr:
                    # For non-pointer types we only need to create one variable
                    # since the original value will not be modified and thus
                    # will not need to be verified
                    f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                    arg_string += f"{arg.spelling}, "

                elif arg.type_spelling == "void*":
                    # We cannot auto-generate harnesses for 
                    # functions that require void pointers
                    failed_generation = True
                    fail_msg = f"Function requires a 'void* {arg.spelling}' argument: {change.old}"
                    break
                else:
                    f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                    arg_string += f"{arg.spelling}, "

        if not failed_generation:
            arg_string = arg_string.removesuffix(", ")

            # 2. Preconditions
            # Any __assume statements about the input that we need to incorporate

            # 3. Call the functions under verification
            ret_type = change.old.ident.type_spelling

            f.write(f"{INDENT}{ret_type} ret_old = ")
            f.write(f"{change.old.ident.spelling}{CONFIG.SUFFIX}({arg_string});\n")

            suffix = CONFIG.SUFFIX if identity else ''
            f.write(f"{INDENT}{ret_type} ret = ")
            f.write(f"{change.new.ident.spelling}{suffix}({arg_string});\n\n")

            # 4. Postconditions
            #   Verify equivalance with one or more assertions
            f.write(f"{INDENT}__CPROVER_assert(ret_old == ret, \"{CONFIG.CBMC_ASSERT_MSG}\");")

            # Enclose driver function
            f.write(f"\n}}\n#endif\n")

    if failed_generation:
        os.remove(harness_path)
        print_err(fail_msg)
        return False
    else:
        return True

def log_harness(filename: str,
        func_name: str,
        identity: bool,
        result: AnalysisResult,
        start_time: datetime,
        driver: str,
        change: DependencyFunctionChange) -> None:
    if CONFIG.ENABLE_RESULT_LOG:
        if not os.path.exists(filename):
            f = open(filename, mode='w', encoding='utf8')
            f.write("func_name;identity;result;runtime;driver;old_src;new_src\n")
        else:
            f = open(filename, mode='a', encoding='utf8')

        runtime = datetime.now() - start_time
        f.write(f"{func_name};{identity};{result.name};{runtime};{driver};{change.old.filepath};{change.new.filepath}\n")
        f.close()

def run_harness(change: DependencyFunctionChange, script_env: dict[str,str],
        driver: str, func_name: str, log_file: str, current: int, total: int, quiet: bool) -> bool:
    ''' 
    Returns True if the assertion in the harness
    was successful
    '''
    script_env.update({
        'DRIVER': driver,
        'FUNC_NAME': func_name,
    })

    out = subprocess.DEVNULL if quiet else sys.stderr
    identity = driver.endswith(f"{CONFIG.IDENTITY_HARNESS}.c")

    time_start(f"{'(ID) ' if identity else ''}Starting CBMC analysis for {change.old}: {os.path.basename(driver)} ({current}/{total})")
    wait_on_cr()

    start = datetime.now()
    driver_name = os.path.basename(driver)

    if CONFIG.CBMC_TIMEOUT <= 0:
        log_harness(log_file,func_name,identity,AnalysisResult.TIMEOUT,start,driver,change)
        time_end(f"Execution timed-out for {driver_name}",  start, AnalysisResult.TIMEOUT)
        return False

    try:
        p = subprocess.Popen([ CONFIG.CBMC_SCRIPT ],
            env = script_env, stdout = out, stderr = out, cwd = BASE_DIR,
            start_new_session = True
        )
        p.wait(timeout=CONFIG.CBMC_TIMEOUT)
        return_code = p.returncode
    except KeyboardInterrupt:
        os.killpg(os.getpgid(p.pid), signal.SIGTERM) # type: ignore

        log_harness(log_file,func_name,identity,AnalysisResult.INTERRUPT,start,driver,change)
        print("\n")
        time_end(f"Cancelled execution for {driver_name}",  start, AnalysisResult.INTERRUPT)
        return False
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(p.pid), signal.SIGTERM) # type: ignore

        log_harness(log_file,func_name,identity,AnalysisResult.TIMEOUT,start,driver,change)
        time_end(f"Execution timed-out for {driver_name}",  start, AnalysisResult.TIMEOUT)
        return False

    match return_code:
        case AnalysisResult.NO_VCCS.value:
            msg = f"No verification conditions generated for: {driver}"
        case AnalysisResult.FAILURE.value:
            msg = f"Identity verification failed: {func_name}" if identity else \
                    f"Verification failed: {func_name}"
        case AnalysisResult.SUCCESS.value:
            msg = f"Identity verification successful: {func_name}" if identity else \
                    f"Verification successful: {func_name}"
        case _:
            if not os.path.exists(f"{CONFIG.OUTDIR}/{CONFIG.CBMC_OUTFILE}"):
                msg = f"An error occured during goto-cc compilation of {driver}"
            else:
                msg = f"An error occured during the analysis of {driver}"
            if CONFIG.DIE_ON_ERROR:
                print_err(msg)
                sys.exit(return_code)

    log_harness(log_file,func_name,identity,AnalysisResult(return_code),start,driver,change)

    time_end(msg,  start, AnalysisResult(return_code))

    return return_code == AnalysisResult.SUCCESS.value
