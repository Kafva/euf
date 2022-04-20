from datetime import datetime
import os, subprocess, sys, signal, json
import shutil

from clang import cindex
from cparser import BASE_DIR, CONFIG, AnalysisResult, \
        DependencyFunctionChange, FunctionState, SourceDiff
from cparser.util import print_result, time_end, time_start, wait_on_cr, print_err


def valid_preconds(change: DependencyFunctionChange, iflags: dict[str,set[str]],
        logfile: str= "", quiet:bool = False) -> bool:
    '''
    If a change passes this function, it should be possible 
    to create a harness for it.
    '''
    func_name = change.old.ident.spelling
    result = AnalysisResult.SUCCESS
    fail_msg = ""

    # There exists compilation instructions for the TU the function is defined in
    if not change.old.filepath in iflags or len(iflags[change.old.filepath]) == 0:
        fail_msg = f"Skipping {func_name}() due to missing compilation instructions for {change.old.filepath}"
        result = AnalysisResult.MISSING_COMPILE

    # The number-of arugments and their types have not changed
    elif (old_cnt := len(change.old.arguments)) != \
        (new_cnt := len(change.new.arguments)):
        fail_msg = f"Differing number of arguments: a/{old_cnt} -> b/{new_cnt} in {change}"
        result = AnalysisResult.DIFF_ARG_CNT

    # The return-type has not changed
    elif change.old.ident != change.new.ident:
        fail_msg = \
            f"Different return type: a/{change.old.ident.type_spelling} " + \
            f"-> b/{change.old.ident.type_spelling} in {change}"
        result = AnalysisResult.DIFF_RET

    # Function does not have a void return value
    elif change.old.ident.type_spelling == "void":
        fail_msg = f"Cannot verify function with a 'void' return value: {change.old}"
        result = AnalysisResult.VOID_RET

    # Function has at least one parameter
    elif len(change.old.arguments) == 0:
        fail_msg = f"Cannot verify a function with zero arguments: {change.old}"
        result = AnalysisResult.NO_ARGS
    else:
        # The paramter types have not changed
        for a1,a2 in zip(change.old.arguments,change.new.arguments):
            if a1!=a2:
                fail_msg = f"Different argument types: a/{a1} -> b/{a2} in {change}"
                result = AnalysisResult.DIFF_ARG_TYPE
                break

        if result == AnalysisResult.SUCCESS:
            # We cannot auto-generate harnesses for functions that require void pointers
            for arg in change.old.arguments:
                if arg.type_spelling == "void*":
                    fail_msg = f"Function requires a 'void* {arg.spelling}' argument: {change.old}"
                    result = AnalysisResult.VOID_ARG
                    break

    if result != AnalysisResult.SUCCESS:
        if logfile != "":
            log_harness(logfile, func_name, None, result, None, "", change)
        if not quiet:
            print_result(fail_msg, result)
        return False
    else:
        return True

def get_I_flags_from_tu(diffs: list[SourceDiff], old_dir: str, old_src_dir:str ) -> dict[str,set[str]]:
    '''
    Return a dict with paths (prepended with -I) to the directories
    which need to be available with '-I' during goto-cc compilation for each TU
    '''
    base_paths = { d.new_path: set()   for d in diffs }
    new_names =  [ d.new_path for d in diffs ]

    with open(f"{old_src_dir}/compile_commands.json", mode='r', encoding='utf8') as f:
        for tu in json.load(f):
            basename = tu['file'].removeprefix(old_dir.rstrip("/")+"/")
            if basename in new_names:
                for arg in tu['arguments']:
                    if arg.startswith("-I"):
                        # Add the include path as an absolute path
                        base_paths[basename].add(f"-I{tu['directory']}/{arg[2:]}")

    return base_paths

def add_includes_from_tu(diff: SourceDiff, old_dir: str, old_src_dir:str, iflags: dict[str,set[str]],
        tu_includes: dict[str,tuple[list[str],list[str]]]) -> None:
    '''
    Adds the set of all the headers that are included into the TU to the provided object
    that corresponds to the given diff split into headers under /usr/inlcude
    and project specific headers.
    The usr headers will be included with <...> in drivers and the others
    will be included using "...", these files will be included using
    the basepath to the dependency which is on the include path of the driver

    Note that the order of includes matter so we want to use a list

    libexpat has certain "_impl" source files which are included by other files
    and lack any include statements of their own.

    We give the _impl files the same includes as the first file that
    included them (provided that they lack includes of their own)
    '''
    tu_old = cindex.TranslationUnit.from_source(
            f"{old_dir}/{diff.old_path}",
            args = diff.old_compile_args
    )
    usr_includes = []
    project_includes = []
    included_c_files = []
    base_include_paths = [ f[2:] for f in iflags ]

    for inc in tu_old.get_includes():
        hdr_path = inc.include.name

        # Record if any .c files are included
        if hdr_path.endswith(".c"):
            trimmed = hdr_path.removeprefix(old_dir).strip('/')
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
            hdr_path = hdr_path.removeprefix(old_src_dir+"/")
            for include_path in base_include_paths:
                hdr_path = hdr_path.strip("/").removeprefix(include_path) \
                    .strip("/")
                if os.path.basename(hdr_path) in CONFIG.BLACKLISTED_HEADERS:
                    continue

                if not hdr_path in project_includes:
                    project_includes.append(hdr_path)

    # Add all of the headers from the current TU to the C files
    # that it includes
    #
    # Also add the include flags from the 'parent'
    for c_file in included_c_files:
        tu_includes[c_file]    = (usr_includes, project_includes)
        iflags[c_file]         = iflags[diff.old_path]

    if len(usr_includes) > 0 or len(project_includes) > 0:
        tu_includes[diff.old_path] = (usr_includes, project_includes)

def create_harness(change: DependencyFunctionChange, harness_path: str,
        includes: tuple[list[str],list[str]], function_state: FunctionState, identity: bool = False) -> None:
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
    INDENT=CONFIG.INDENT

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

        # Any custom include directives for the specific file
        # Note that these are included _before_ standard project includes
        filename = os.path.basename(change.old.filepath)
        if filename in CONFIG.CUSTOM_HEADERS:
            f.write("\n")
            for header in CONFIG.CUSTOM_HEADERS[filename]:
                header = os.path.expanduser(header)
                if header.startswith("/") and os.path.isfile(header):
                    # The header is a custom header that should be copied to .out
                    header_name = os.path.basename(header)
                    shutil.copy(header, f"{CONFIG.OUTDIR}/{header_name}")
                else:
                    # The header references an internal file in the project
                    header_name = header

                f.write(f"#include \"{header_name}\"")
            f.write("\n\n")

        f.write("\n")

        # Project include directives
        for header in includes[1]:
            f.write(f"#include \"{header}\"\n")

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
        arg_string_old = ""
        arg_string = ""
        SUFFIX = CONFIG.SUFFIX
        unequal_inputs = False

        # Note that all checks for e.g. void params are done before calling create_harness()
        for arg in change.old.arguments:

            # If the function takes a paramter whose type has been renamed, 
            #   e.g. OnigEncodingTypeST or usbi_os_backend
            # we cannot perform any meaningful verification unless we are able
            # to initialise each seperate field and create assumptions for each one
            # that the _old and regular objects are equal in every way except their
            # function_ptr fields (TODO)
            #
            # For now, we just initalise both as nondet(), meaning that a passing equivalance
            # check would infer a pass for all (unrelated) possible values of the parameter.
            # A SUCCESS result for this limited harness would still be sound but it would
            # need to produce the same output regardless of what values the input has
            # (since it is no longer synced between the calls)
            base_type = arg.type_spelling.removeprefix("struct").strip(' *')

            if base_type in CONFIG.EXPLICIT_RENAME:
                unequal_inputs = True

                type_str = arg.explicitly_renamed_type()
                f.write(f"{INDENT}{type_str} {arg.spelling}{SUFFIX};\n"  )

                arg_string_old += f"{arg.spelling}{SUFFIX}, "

                f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                arg_string += f"{arg.spelling}, "

            elif not arg.is_ptr:
                # For non-pointer types we only need to create one variable
                # since the original value will not be modified and thus
                # will not need to be verified
                f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                arg_string_old += f"{arg.spelling}, "
                arg_string += f"{arg.spelling}, "
            else:
                # Argument initialisation
                f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                arg_string_old += f"{arg.spelling}, "
                arg_string += f"{arg.spelling}, "

        arg_string_old = arg_string_old.removesuffix(", ")
        arg_string = arg_string.removesuffix(", ")

        # 2. Preconditions
        # Create assumptions for any arguments that were identified as only being
        # called with deterministic values
        f.write("\n")
        for idx,param in enumerate(function_state.parameters):
            if not param.nondet and len(param.states) > 0:
                arg_name = change.old.arguments[idx].spelling
                f.write(f"{INDENT}__CPROVER_assume(\n")

                out_string = ""
                for state in param.states:
                    state_val  = state if str(state).isnumeric() else f"\"{state}\""
                    out_string += f"{INDENT}{INDENT}{arg_name} == {state_val} ||\n"

                out_string = out_string.removesuffix(" ||\n")

                f.write(f"{out_string}\n{INDENT});\n")
        f.write("\n")

        # 3. Call the functions under verification
        ret_type = change.old.ident.type_spelling

        if unequal_inputs and not identity:
            f.write(f"{INDENT}// Unequal input comparsion\n")

        f.write(f"{INDENT}{ret_type} ret_old = ")
        f.write(f"{change.old.ident.spelling}{SUFFIX}({arg_string_old});\n")

        f.write(f"{INDENT}{ret_type} ret = ")
        if identity:
            f.write(f"{change.new.ident.spelling}{SUFFIX}({arg_string_old});\n\n")
        else:
            f.write(f"{change.new.ident.spelling}({arg_string});\n\n")


        # 4. Postconditions
        #   Verify equivalance with one or more assertions
        f.write(f"{INDENT}__CPROVER_assert(ret_old == ret, \"{CONFIG.CBMC_ASSERT_MSG}\");")

        # Enclose driver function
        f.write(f"\n}}\n#endif\n")

def log_harness(filename: str,
    func_name: str,
    identity: bool|None,
    result: AnalysisResult,
    start_time: datetime|None,
    driver: str,
    change: DependencyFunctionChange) -> None:
    '''
    We allow None as a parameter for cases where pre-analysis checks fail
    '''
    if CONFIG.ENABLE_RESULT_LOG:
        if not os.path.exists(filename):
            f = open(filename, mode='w', encoding='utf8')
            f.write("func_name;identity;result;runtime;driver;old_src;new_src\n")
        else:
            f = open(filename, mode='a', encoding='utf8')

        runtime = datetime.now() - start_time if start_time else ""

        f.write(f"{func_name};{identity};{result.name};{runtime};{driver};{change.old.filepath};{change.new.filepath}\n")
        f.close()

def run_harness(change: DependencyFunctionChange, script_env: dict[str,str],
    driver: str, func_name: str, log_file: str, current: int, total: int,
    dep_i_flags:str, quiet: bool) -> bool:
    '''
    Returns True if the assertion in the harness
    was successful
    '''
    script_env.update({
        'DRIVER': driver,
        'FUNC_NAME': func_name,
        'DEP_I_FLAGS': dep_i_flags
    })

    out = subprocess.PIPE if quiet else sys.stderr
    identity = driver.endswith(f"{CONFIG.IDENTITY_HARNESS}.c")

    id_str = '(ID) ' if identity else ''
    time_start(f"{id_str}Starting CBMC analysis for {change.old}: " +
               f"{os.path.basename(driver)} ({current}/{total})"
    )
    wait_on_cr()

    start = datetime.now()
    driver_name = os.path.basename(driver)

    if CONFIG.CBMC_TIMEOUT <= 0:
        log_harness(log_file,func_name,identity,AnalysisResult.TIMEOUT,start,driver,change)
        time_end(f"Execution timed-out for {driver_name}",  start, AnalysisResult.TIMEOUT)
        return False

    output = ""

    try:
        p = subprocess.Popen([ CONFIG.CBMC_SCRIPT ],
            env = script_env, stdout = out, stderr = out, cwd = BASE_DIR,
            start_new_session = True
        )
        p.wait(timeout=CONFIG.CBMC_TIMEOUT)

        if quiet:
            output = p.stdout.read().decode('utf8')  # type: ignore
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
        case AnalysisResult.NO_BODY.value:
            msg = f"No body available for {func_name}"
        case AnalysisResult.NO_VCCS.value:
            msg = f"No verification conditions generated for: {driver}"
        case AnalysisResult.FAILURE.value:
            msg = f"Identity verification failed: {func_name}" if identity else \
                    f"Verification failed: {func_name}"
        case AnalysisResult.SUCCESS.value:
            msg = f"Identity verification successful: {func_name}" if identity else \
                    f"Verification successful: {func_name}"
        case _:
            if return_code == AnalysisResult.STRUCT_CNT_CONFLICT.value:
                msg = f"Differing member count in one or more structs"
            elif return_code == AnalysisResult.STRUCT_TYPE_CONFLICT.value:
                msg = f"Type conflict in one or more structs"
            elif not os.path.exists(f"{CONFIG.OUTDIR}/{CONFIG.CBMC_OUTFILE}"):
                msg = f"An error occured during goto-cc compilation of {driver}"
            else:
                msg = f"An error occured during the analysis of {driver}"

            if CONFIG.DIE_ON_ERROR:
                print(output)
                print_err(msg)
                sys.exit(return_code)

    log_harness(log_file,func_name,identity,AnalysisResult(return_code),start,driver,change)

    time_end(msg,  start, AnalysisResult(return_code))

    return return_code == AnalysisResult.SUCCESS.value
