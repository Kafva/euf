from datetime import datetime
import os, subprocess, sys
import shutil

from clang import cindex
from cparser import BASE_DIR, CONFIG, DependencyFunctionChange, SourceDiff
from cparser.util import print_err, print_stage, time_end, time_start

def get_includes_for_tu(diff: SourceDiff, old_root_dir: str) -> tuple[list[str],list[str]]:
    '''
    Return a set of all the headers that are included into the TU 
    that corresponds to the given diff split into headers under /usr/inlcude
    and project specific headers.
    The usr headers will be included with <...> in drivers and the others
    will be included using "...", these files will be autaomtaically copied into the
    OUTDIR directory which is on the include path of the driver

    Note that the order of includes matter so we want to use a list
    '''
    tu_old = cindex.TranslationUnit.from_source(
            f"{old_root_dir}/{diff.old_path}",
            args = diff.old_compile_args
    )
    usr_includes = []
    project_includes = []

    for inc in tu_old.get_includes():
        if not inc.is_input_file:
            hdr_path = inc.include.name
            if hdr_path.startswith("/usr/include/"):
                # Skip system headers under certain specified paths
                if any([ hdr_path.startswith(f"/usr/include/{skip_header}") \
                        for skip_header in CONFIG.SKIP_HEADERS_UNDER ]):
                    continue

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

                project_includes.append(hdr_path)

    return (usr_includes, project_includes)

def create_harness(change: DependencyFunctionChange, dep_path: str,
        includes: tuple[list[str],list[str]],  identity: bool = False) -> tuple[str,str]:
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

    Returns a tuple with the path to the harness and 
    an empty string on success, otherwise an error message is 
    given at the second index

    If "identity" is set, the comparsion will be made with the old version
    and itself, creating a seperate harness file with the suffix _id
    '''
    harness_path = ""

    # ~~Basic assumptions for harness generation~~
    # The number-of arugments and their types have not changed

    if not identity:
        if (old_cnt := len(change.old.arguments)) != \
            (new_cnt := len(change.new.arguments)):
            return ("", f"Differing number of arguments: a/{old_cnt} -> b/{new_cnt}")

        for a1,a2 in zip(change.old.arguments,change.new.arguments):
            if a1!=a2:
                return ("", f"Different argument types: a/{a1} -> b/{a2}")

        # The return-type has not changed
        if change.old.ident != change.new.ident:
            return ("", f"Different return type: a/{change.old.ident.type_spelling} -> b/{change.old.ident.type_spelling}")

    harness_dir = f"{dep_path}/{CONFIG.HARNESS_DIR}"
    if not os.path.exists(harness_dir):
        os.mkdir(harness_dir)
    harness_path = f"{harness_dir}/{change.old.ident.spelling}{CONFIG.IDENTITY_HARNESS if identity else ''}.c"

    INDENT=CONFIG.INDENT
    failed_generation = False
    fail_msg = ""

    # Write the harness
    with open(harness_path, mode='w', encoding='utf8') as f:
        # Debug information
        f.write(f"// {change}\n")

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
        f.write(f"\n{change.old.prototype_string(CONFIG.SUFFIX)};")

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
        f.write(f"\n{change.new.prototype_string()};\n\n")

        # Entrypoint function
        f.write(f"void {CONFIG.EUF_ENTRYPOINT}() {{\n{INDENT}#ifdef CBMC\n")

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
            fail_msg = "Cannot verify function with a 'void' return value"
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
                    fail_msg = f"Function requires a 'void*' argument: {arg.spelling}"
                    break
                else:
                    f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                    arg_string += f"{arg.spelling}, "

                    #failed_generation = True
                    #fail_msg = f"Unable to initialise argument of type: {arg.type_spelling}"
                    #break

        if not failed_generation:
            arg_string = arg_string.removesuffix(", ")

            # 2. Preconditions
            # Any __assume statements about the input that we need to incorporate

            # 3. Call the functions under verification
            ret_type = change.old.ident.type_spelling

            f.write(f"{INDENT}{ret_type} ret_old = ")
            f.write(f"{change.old.ident.spelling}{CONFIG.SUFFIX}({arg_string});\n")

            f.write(f"{INDENT}{ret_type} ret = ")
            f.write(f"{change.new.ident.spelling}{CONFIG.SUFFIX if identity else ''}({arg_string});\n\n")

            # 4. Postconditions
            #   Verify equivalance with one or more assertions
            f.write(f"{INDENT}__CPROVER_assert(ret_old == ret, \"{CONFIG.CBMC_ASSERT_MSG}\");")

            # Enclose driver function
            f.write(f"\n{INDENT}#endif\n}}\n")

    if failed_generation:
        os.remove(harness_path)
        return ("", fail_msg)
    else:
        return (harness_path, "")

def run_harness(change: DependencyFunctionChange, script_env: dict[str,str],
        driver: str, func_name: str, quiet: bool) -> bool:
    ''' 
    Returns True if the harness assertion in the harness
    was successful
    '''
    script_env.update({
        'DRIVER': driver,
        'FUNC_NAME': func_name,
    })

    out = subprocess.DEVNULL if quiet else sys.stderr

    time_start(f"Starting CBMC analysis for {change.old}: {os.path.basename(driver)}")
    if driver.endswith(f"{CONFIG.IDENTITY_HARNESS}.c"):
        print_stage("Identity verification")

    start = datetime.now()
    driver_name = os.path.basename(driver)

    try:
        return_code = subprocess.run([ CONFIG.CBMC_SCRIPT ],
            env = script_env, stdout = out, stderr = out, cwd = BASE_DIR,
            timeout = CONFIG.CBMC_TIMEOUT
        ).returncode
    except KeyboardInterrupt:
        print("\n")
        time_end(f"Cancelled execution for {driver_name}",  start)
        return False
    except subprocess.TimeoutExpired:
        time_end(f"Execution timed-out for {driver_name}",  start)
        return False


    time_end(f"Finished CBMC analysis for {driver_name}",  start)

    match return_code:
        case 0:
            return True
        # SUCCESS verification: equivalent change
        case 53:
        # "SUCCESS": No verification conditions generated
            print_err(f"No verification conditions generated for: {driver}")
            return False
        case 54:
        # FAILED verification: non-equivalent change
            return False
        case _:
        # ERROR
            if not os.path.exists(f"{CONFIG.OUTDIR}/{CONFIG.CBMC_OUTFILE}"):
                print_err(f"An error occured during goto-cc compilation of {driver}")
            else:
                print_err(f"An error occured during the analysis of {driver}")
            sys.exit(return_code)
