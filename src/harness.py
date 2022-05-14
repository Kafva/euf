import os, subprocess, sys, signal, json, shutil
from datetime import datetime
from clang import cindex

from src import BASE_DIR, ERR_EXIT
from src.config import CONFIG
from src.fmt import fmt_change, fmt_location
from src.types import AnalysisResult, DependencyFunctionChange, \
    FunctionState, IdentifierLocation, SourceDiff
from src.util import add_to_timeout_blacklist, ccdb_dir, load_timeout_blacklist, \
        print_result, shorten_path_fields, \
        time_end, time_start, print_err

def invalid_preconds(change: DependencyFunctionChange,
  include_paths: dict[str,set[str]],
  skip_renaming: set[str],
  logfile: str= "", quiet:bool = False,ignore_timeout:bool=False) \
  -> int:
    '''
    If a change passes this function, it should be possible
    to create a harness for it. Returns the number of failed checks.

    To allow for analysis regarding the most common reasons for why analysis
    failed we need to return a set() of analysis results since e.g. a function 
    could have both a different argument count and different argument types.

    For the log to contain useful information from a CIA perspective, the order
    of the checks is relevant. E.g. we want to be notified if the argument count
    differs regardless of if a function has a void return value
    '''
    func_name = change.old.ident.location.name
    results = set()
    fail_msg = ""
    change_str = fmt_change(change)
    old_loc_str = fmt_location(change.old.ident.location)

    def check_param_types(results: set[AnalysisResult],
      change:DependencyFunctionChange) -> tuple[set[AnalysisResult],str]:
        param_msg = ""
        for a1,a2 in zip(change.old.arguments,change.new.arguments):
            if a1!=a2:
                param_msg = f"Different argument types: a/{a1} -> b/{a2} "\
                           f"in {change_str}"
                results.add(AnalysisResult.DIFF_ARG_TYPE)
                break

        if len(results) == 0:
            # We cannot auto-generate harnesses for
            # functions that require void pointers
            for arg in change.old.arguments:
                if arg.type_spelling == "void*":
                    param_msg = \
                        f"Function requires a 'void* {arg.location.name}' "\
                        f"argument: {old_loc_str}"
                    results.add(AnalysisResult.VOID_ARG)
                    break

        return results, param_msg

    # Previous analysis attempts for the function have timed-out
    # and we therefore exclude new attempts
    if func_name in load_timeout_blacklist() and not ignore_timeout:
        fail_msg = f"Skipping {func_name}() due to previous TIMEOUT"
        results.add(AnalysisResult.PREV_TIMEOUT)
    # Compilation instructions for the TU that the
    # function is defined in do not exist
    if not change.old.ident.location.filepath in include_paths or \
       len(include_paths[change.old.ident.location.filepath]) == 0:
        path = change.old.ident.location.filepath
        fail_msg = \
            f"Skipping {func_name}() due to missing compilation "\
            f"instructions for {path}"
        results.add(AnalysisResult.MISSING_COMPILE)
    # The number-of arguments or their types have changed)
    if (old_cnt := len(change.old.arguments)) != \
        (new_cnt := len(change.new.arguments)):
        fail_msg = f"Differing number of arguments: a/{old_cnt} -> "\
                   f"b/{new_cnt} in {change_str}"
        results.add(AnalysisResult.DIFF_ARG_CNT)
    # The return-type has changed
    if change.old.ident != change.new.ident:
        fail_msg = \
            f"Different return type: a/{change.old.ident.type_spelling} " \
            f"-> b/{change.new.ident.type_spelling} in {change_str}"
        results.add(AnalysisResult.DIFF_RET)

    # Parameter types have changed (or a void parameter exists)
    if (tpl := check_param_types(results,change))[0] != AnalysisResult.SUCCESS:
        results |= tpl[0]
        if tpl[1]!="":
            fail_msg = tpl[1]

    # One or more arguments are of types that have been explicitly renamed
    if any(a.type_spelling.removeprefix("struct ").strip(' *') in \
          CONFIG.EXPLICIT_RENAME for a in change.old.arguments):
        fail_msg = f"Verification is not supported for functions where one or "\
                   "more parameter types have been explicitly renamed: "\
                   f"{old_loc_str}"
        results.add(AnalysisResult.RENAMED_TYPE)
    # The function has not been given an '_old' suffix, preventing analysis
    if func_name in skip_renaming:
        fail_msg = f"Renaming {func_name}() could cause conflicts, skipping " +\
            change_str
        results.add(AnalysisResult.NOT_RENAMED)
    # Function has a void return value
    if change.old.ident.type_spelling == "void":
        fail_msg = f"Cannot verify function with a 'void' "\
                   f"return value: {old_loc_str}"
        results.add(AnalysisResult.VOID_RET)
    # Function has zero parameters
    if len(change.old.arguments) == 0:
        fail_msg = f"Cannot verify a function with zero arguments: "\
                   f"{old_loc_str}"
        results.add(AnalysisResult.NO_ARGS)
    # Array argument(s)
    if any(str(a).find("[") != -1 for a in change.old.arguments):
        fail_msg = f"Verifying functions with array '[]' parameter(s) is "\
                   f"not supported: {old_loc_str}"
        results.add(AnalysisResult.ARRAY_ARG)
    # Variadic function
    if change.old.ident.is_varidiac_function:
        fail_msg = f"Variadic functions are not supported "\
                   f"for verification: {old_loc_str}"
        results.add(AnalysisResult.VARIADIC)
    # More than two levels of pointer indirection in one or more arguments
    if any(str(a).count("*") >= 3 for a in change.old.arguments):
        fail_msg = f"Function parameter(s) are only allowed to have two "\
                   "or fewer levels of indirection ('*'): "\
                   f"{old_loc_str}"
        results.add(AnalysisResult.INDIRECTION_LIMIT)

    if len(results) != 0:
        if logfile != "":
            log_harness(logfile, func_name, None, results, None, "", change)
        if not quiet:
            if len(results)>1:
                fail_msg += f" -- {len(results)-1} additional precondition "\
                "failure(s)"
            print_result(fail_msg, next(iter(results)) )

    return len(results)

def get_include_paths_for_tu(diffs: list[SourceDiff], source_dir_old:str) \
 -> dict[str,set[str]]:
    '''
    Return a dict with paths (prepended with -I) to the directories
    which need to be available with '-I' during goto-cc compilation for each TU
    by parsing each entry in the ccdb
    '''
    include_paths = { d.filepath_old: set() for d in diffs }
    filepaths_old =  [ d.filepath_old for d in diffs ]

    with open(f"{source_dir_old}/compile_commands.json", mode='r', encoding='utf8') as f:
        for tu in json.load(f):
            # We assume that all files are given with an abspath in ccdb
            assert tu['file'].startswith("/")

            if tu['file'] in filepaths_old:
                for arg in tu['arguments']:
                    if arg.startswith("-I"):
                        if arg[2] == "/": # abspath
                            include_path = f"-I{arg[2:]}"
                        else: # Translate relative to absolute
                            include_path = f"-I{tu['directory']}/{arg[2:]}"
                        include_paths[tu['file']].add(include_path)

    return include_paths


def add_includes_from_tu(diff: SourceDiff, include_paths: dict[str,set[str]],
 tu_includes: dict[str,tuple[list[str],list[str]]]) -> None:
    '''
    Go through all #include directives in the old version of the file in the
    provided `diff` object and add them to the `tu_includes` array.

    /usr headers will be included with <...> in drivers and the others
    will be included using "...", these files will be included using
    the basepath to the dependency which is on the include path of the driver

    Note that the order of includes matter so we want to use a list

    libexpat has certain "_impl" source files which are included by other files
    and lack any include statements of their own.

    We give the _impl files the same includes as the first file that
    included them (provided that they lack includes of their own)
    '''
    os.chdir(diff.compile_dir_old)
    tu_old = cindex.TranslationUnit.from_source(
            diff.filepath_old,
            args = diff.compile_args_old
    )
    usr_includes = []
    project_includes = []
    included_c_files = []

    source_dir_old = ccdb_dir(new=False)

    # Extract the base include paths relevant for this TU
    # [2:] removes '-I' and abspath() is needed to resolve relative paths
    include_paths_for_tu = [ os.path.abspath(f[2:])
            for f in include_paths[diff.filepath_old]
    ]

    # Unless we sort the include paths in a canonical manner, the #include
    # paths in harnesses can differ between runs which can be confusing
    sorted_include_paths = sorted(list(include_paths_for_tu))

    for inc in tu_old.get_includes():
        hdr_path = inc.include.name

        # Record if any .c files are included
        if hdr_path.endswith(".c"):
            trimmed = hdr_path.removeprefix(source_dir_old).strip('/')
            included_c_files.append(trimmed)
            continue


        if hdr_path.startswith("/usr"):
            # Skip system headers under certain specified paths
            if any( hdr_path.startswith(f"/usr/{skip_header}") \
               for skip_header in CONFIG.SKIP_HEADERS_UNDER):
                continue

            if not hdr_path in usr_includes:
                for system_include_prefix in CONFIG.SYSTEM_INCLUDE_PREFIXES:
                    hdr_path = hdr_path.removeprefix(system_include_prefix+"/")

                usr_includes.append(hdr_path)
        else:
            # Translate the header to an abspath(),
            # reliant on the os.chdir() command at the start
            # of the function to work correctly
            hdr_path = os.path.abspath(hdr_path)

            for include_path in sorted_include_paths:
                if os.path.basename(hdr_path) in CONFIG.BLACKLISTED_HEADERS:
                    break

                # Each 'include_path' must be an absolute path
                # Otherwise, startswith() will not work as intended
                if hdr_path.startswith(include_path+"/"):
                    # We use +'/' since the include path does not have a
                    # trailing slash, without this we will get incorrect paths
                    #   e.g.    "/lib/st.h" rather than "lib/st.h"
                    hdr_path = hdr_path.removeprefix(include_path+"/")

                    if hdr_path not in project_includes:
                        project_includes.append(hdr_path)
                    break

    # Add all of the headers from the current TU to the C files
    # that it includes and the include flags from the 'parent'
    for c_file in included_c_files:
        tu_includes[c_file]    = (usr_includes, project_includes)
        include_paths[c_file]  = include_paths[diff.filepath_old]

    if len(usr_includes) > 0 or len(project_includes) > 0:
        tu_includes[diff.filepath_old] = (usr_includes, project_includes)

def create_harness(change: DependencyFunctionChange, harness_path: str,
  includes: tuple[list[str],list[str]], function_state: FunctionState,
  identity: bool = False) -> None:
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

    If "identity" is set, the comparison will be made with the old version
    and itself, creating a separate harness file with the suffix _id
    '''
    indent=CONFIG.INDENT

    # Write the harness
    with open(harness_path, mode='w', encoding='utf8') as f:
        # Debug information
        f.write(f"// {fmt_change(change)}\n")

        # ifdef to prevent linting warnings
        f.write("#ifdef CBMC\n")

        # System include directives
        for header in includes[0]:
            f.write(f"#include <{header}>\n")

        f.write("\n")

        # Any custom include directives for the specific file
        # Note that these are included _before_ standard project includes
        filename = os.path.basename(change.old.ident.location.filepath)
        if filename in CONFIG.CUSTOM_HEADERS:
            f.write("\n")
            for header in CONFIG.CUSTOM_HEADERS[filename]:
                header = os.path.expanduser(header)
                if header.startswith("/") and os.path.isfile(header):
                    # The header is a custom header that should 
                    # be copied to .out
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
            f.write(f"#include \"{header.lstrip('./')}\"\n")
        f.write("\n")

        # nondet() stub declarations
        types = set()
        for arg in change.old.arguments:
            # Note that pointers do not get their own stub declarations
            # We instead assign a nondet() value from the base type 
            # to the dereferenced version.
            type_str = arg.__repr__(type_only=True).strip(' *')
            if type_str not in types:
                f.write(f"{type_str} "
                    f"{arg.nondet_prototype()};\n"
                )
                types.add(type_str)

        # Declaration of the old version of the function
        f.write(f"\n{change.old.prototype_string(CONFIG.SUFFIX)};\n")

        if not identity:
            # Declaration for the new version of the function
            #
            # In some cases the function will already be declared in of
            # the headers but providing a second declaration in the driver does
            # not cause issues
            #
            # NOTE: if the function is declared as 'static'
            # in one of the included headers we will not be able to access
            # it a warning akin to
            #
            # **** WARNING: no body for function <...>
            #
            # will show up during the CBMC analysis if this occurs
            f.write(f"{change.new.prototype_string()};\n")

        f.write("\n")

        # Entrypoint function
        f.write(f"void {CONFIG.EUF_ENTRYPOINT}() {{\n")

        # ~~ Harness components ~~
        # https://github.com/model-checking/cbmc-starter-kit/wiki/Frequently-Asked-Questions
        #
        # We are not bound to the `nondet_` symbols defined by CBMC
        # internally, any function prefixed with nondet_ is treated as a special
        # case by CBMC and we can thus create our own versions
        # by writing a prototype string for them with the return type we desire
        #  http://www.cprover.org/cprover-manual/modeling/nondeterminism/

        # 1. Initialization
        # The initialisation involves creating valid, unconstrained and equal
        # data structures that can be passed to the two versions

        # Note that all checks for e.g. void parameters are
        # done before calling create_harness() in valid_preconds()

        # Since we only check return values, we never need to create
        # more than one input variable. If we had been checking pointer
        # modifications then we would need separate variables to pass
        # the old/new version

        # The string that will end up inside of the function calls
        arg_string = ""

        for arg in change.old.arguments:

            is_ptr = arg.type_spelling.count('*')==1
            is_dbl_ptr = arg.type_spelling.count('*')==2

            # The argument type (without any '*' tokens)
            type_str = arg.__repr__(type_only=True).strip(' *')
            decl = arg.__repr__().removeprefix('const ')

            if is_dbl_ptr:
                decl = decl.replace('**','*')

            # ~~ nondet() initialisation ~~
            # ./doc/cprover-manual/modeling-nondeterminism.md
            if is_ptr or is_dbl_ptr:
                f.write(f"{indent}{decl};\n")
                f.write(f"{indent}*{arg.location.name} = "
                        f"{arg.nondet_prototype()};\n")
            else:
                f.write(f"{indent}{arg} = {arg.nondet_prototype()};\n")

            # For double pointers, the argument will be provided
            # with an extra level of indirection
            if is_dbl_ptr:
                arg_string += f"&{arg.location.name}, "
            else:
                arg_string += f"{arg.location.name}, "

        arg_string = arg_string.removesuffix(", ")

        # 2. Preconditions
        # Create assumptions for any arguments that were identified
        # as only being called with deterministic values
        f.write("\n")
        for idx,param in enumerate(function_state.parameters):
            if not param.nondet and len(param.states) > 0:
                arg_name = change.old.arguments[idx].location.name
                f.write(f"{indent}__CPROVER_assume(\n")

                out_string = ""
                # Sort the states to enable file-diff regression testing
                for state in sorted(param.states):
                    state_val  = state if str(state).isnumeric() \
                                       else f"\"{state}\""
                    out_string += f"{indent}{indent}{arg_name} == " \
                                  f"{state_val} ||\n"

                out_string = out_string.removesuffix(" ||\n")

                f.write(f"{out_string}\n{indent});\n")
        f.write("\n")

        # 3. Call the functions under verification
        ret_type = change.old.ident.type_spelling

        f.write(f"{indent}{ret_type} ret_old = ")
        f.write(f"{change.old.ident.location.name}{CONFIG.SUFFIX}"
                f"({arg_string});\n")

        f.write(f"{indent}{ret_type} ret = ")
        if identity:
            f.write(f"{change.new.ident.location.name}{CONFIG.SUFFIX}"
                    f"({arg_string});\n\n")
        else:
            f.write(f"{change.new.ident.location.name}({arg_string});\n\n")


        # 4. Postconditions
        #   Verify equivalence with one or more assertions
        f.write(f"{indent}__CPROVER_assert(ret_old == ret, "
                f"\"{CONFIG.CBMC_ASSERT_MSG}\");\n")

        # Enclose driver function
        f.write("\n}\n#endif\n")

def log_harness(filename: str,
  func_name: str,
  identity: bool|None,
  results: set[AnalysisResult],
  start_time: datetime|None,
  driver: str,
  change: DependencyFunctionChange) -> None:
    '''
    None is allowed as a parameter for cases where pre-analysis checks fail
    '''
    if CONFIG.ENABLE_RESULT_LOG:
        if not os.path.exists(filename):
            f = open(filename, mode='w', encoding='utf8')
            f.write("func_name;identity;result;runtime;driver;"+\
                    IdentifierLocation.csv_header('old') + ";"+\
                    IdentifierLocation.csv_header('new')+"\n"
            )
        else:
            # pylint: disable=consider-using-with
            f = open(filename, mode='a', encoding='utf8')

        runtime = datetime.now() - start_time if start_time else ""
        identity_str = "" if identity is None else identity

        old_loc = shorten_path_fields(change.old.ident.location.to_csv())
        new_loc = shorten_path_fields(change.new.ident.location.to_csv())

        # Sort the results so that they are always printed in the same order
        results_str = ""
        for r in sorted(list(results), key=lambda r: r.name):
            results_str+=f"{r.name},"
        results_str = results_str.removesuffix(",")

        f.write(f"{func_name};{identity_str};{results_str};{runtime};"
                f"{driver};{old_loc};{new_loc}\n")
        f.close()

def run_harness(change: DependencyFunctionChange, script_env: dict[str,str],
  driver: str, func_name: str, log_file: str, current: int, total: int,
  dep_i_flags:str, identity:bool, quiet: bool) -> bool:
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

    loc_str = fmt_location(change.old.ident.location)
    id_str = '(ID) ' if identity else ''
    time_start(f"{id_str}Starting CBMC analysis for {loc_str}(): " +
               f"{os.path.basename(driver)} ({current}/{total})"
    )

    start = datetime.now()
    driver_name = os.path.basename(driver)

    if CONFIG.CBMC_TIMEOUT <= 0:
        log_harness(log_file,func_name,identity,{AnalysisResult.TIMEOUT},
                start,driver,change)
        time_end(f"Execution timed-out for {driver_name}",
                start, AnalysisResult.TIMEOUT)
        return False

    output = ""

    try:
        # pylint: disable=consider-using-with
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

        log_harness(log_file,func_name,identity,{AnalysisResult.INTERRUPT},
                            start,driver,change)
        print("\n")
        time_end(f"Cancelled execution for {driver_name}",
                        start, AnalysisResult.INTERRUPT)
        return False
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(p.pid), signal.SIGTERM) # type: ignore

        log_harness(log_file,func_name,identity,{AnalysisResult.TIMEOUT},
                        start,driver,change)
        time_end(f"Execution timed-out for {driver_name}",
                    start, AnalysisResult.TIMEOUT)

        add_to_timeout_blacklist(func_name)
        return False

    match return_code:
        case AnalysisResult.NO_BODY.value:
            msg = f"No body available for {func_name}"
        case AnalysisResult.NO_VCCS.value:
            msg = f"No verification conditions generated for: {driver}"
        case AnalysisResult.NO_VCCS_UNWIND_FAIL.value:
            msg = f"No verification conditions generated for: " \
                  f"{driver} (incomplete unwinding)"
        case AnalysisResult.FAILURE.value:
            msg = f"Identity verification failed: {func_name}" \
                    if identity else \
                    f"Rejected equivalence assertion: {func_name}"
        case AnalysisResult.SUCCESS.value:
            msg = f"Passed equivalence assertion: {func_name}" \
                    if identity else \
                    f"Verification successful: {func_name}"
        case AnalysisResult.SUCCESS_UNWIND_FAIL.value:
            msg = f"Identity verification successful (incomplete unwinding): "\
                    f"{func_name}" \
                    if identity else \
                    f"Passed equivalence assertion (incomplete unwinding): "\
                    f"{func_name}"
        case AnalysisResult.FAILURE_UNWIND_FAIL.value:
            msg = f"Identity verification failed (incomplete unwinding): "\
                    f"{func_name}" \
                    if identity else \
                    f"Rejected equivalence assertion (incomplete unwinding): {func_name}"
        case _:
            if return_code == AnalysisResult.STRUCT_CNT_CONFLICT.value:
                msg = "Differing member count in one or more structs"
            elif return_code == AnalysisResult.STRUCT_TYPE_CONFLICT.value:
                msg = "Type conflict in one or more structs"
            elif not os.path.exists(f"{CONFIG.OUTDIR}/{CONFIG.CBMC_OUTFILE}"):
                msg = \
                    f"An error occurred during goto-cc compilation of {driver}"
            else:
                msg = f"An error occurred during the analysis of {driver}"

            if CONFIG.DIE_ON_ERROR:
                print(output)
                print_err(msg)
                sys.exit(return_code)
    try:
        analysis_result = AnalysisResult(return_code)
    except ValueError: # => ERROR
        print_err(f"Unexpected return code from CBMC: {return_code}")
        analysis_result = AnalysisResult(ERR_EXIT)

    log_harness(log_file,func_name,identity,{analysis_result},start,driver,change)

    time_end(msg,  start, AnalysisResult(return_code),identity=identity)

    # For identity verification, this return value determines whether or not 
    # full analysis is performed, for full analysis this return value
    # determines if the tested function should be removed from the change set
    return analysis_result in AnalysisResult.results_that_reduce()
