import os, subprocess, sys, traceback
from cparser import BASE_DIR, CONFIG, DependencyFunctionChange
from cparser.util import print_info

def create_harness(change: DependencyFunctionChange, dep_path: str, identity: bool = False) -> tuple[str,str]:
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

    # Write the harness
    with open(harness_path, mode='w', encoding='utf8') as f:
        # Include directives
        for header in CONFIG.STD_HEADERS:
            f.write(f"#include <{header}>\n")
        for header in CONFIG.INCLUDE_HEADERS:
            f.write(f"#include \"{os.path.basename(header)}\"\n")

        # Decleration of the old version of the function
        f.write(f"\n{change.old.prototype_string(CONFIG.SUFFIX)};\n\n")

        # Entrypoint function
        f.write(f"int {CONFIG.EUF_ENTRYPOINT}() {{\n{INDENT}#ifdef CBMC\n")

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
        for arg in change.old.arguments:

            if not arg.is_ptr:
                # For non-pointer types we only need to create one variable
                # since the original value will not be modified and thus
                # will not need to be verified
                f.write(f"{INDENT}{arg.type_spelling} {arg.spelling};\n")
                arg_string += f"{arg.spelling}, "

            else:
                # We cannot auto-generate harnesses for 
                # functions that require void pointers
                if arg.type_spelling == "void*":
                    return ("", f"Function requires a 'void*' argument: {arg.spelling}")

                return ("", f"Unable to initialise argument of type: {arg.typing}")

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
        f.write(f"\n{INDENT}#endif\n{INDENT}return 0;\n}}\n")

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

    print_info(f"Starting CBMC analysis for {change.old}: {os.path.basename(driver)}")
    return_code = subprocess.run([ CONFIG.CBMC_SCRIPT ],
        env = script_env, stdout = out, stderr = out, cwd = BASE_DIR
    ).returncode

    match return_code:
        case 0:
            return True
        # SUCCESS verification: equivalent change
        case 54:
            return False
        # FAILED verification: non-equivalent change
        case _:
        # ERROR
            traceback.print_exc()
            sys.exit(return_code)
