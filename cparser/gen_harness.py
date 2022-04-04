from cparser import DependencyFunctionChange
from cparser.util import print_info

def create_harness(change: DependencyFunctionChange) -> tuple[str,str]:
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
    '''
    harness_path = ""

    # ~~Basic assumptions for harness generation~~
    # The number-of arugments and their types have not changed
    if (old_cnt := len(change.old.arguments)) != \
        (new_cnt := len(change.new.arguments)):
        return ("", f"Differing number of arguments: a/{old_cnt} -> b/{new_cnt}")

    for a1,a2 in zip(change.old.arguments,change.new.arguments):
        if a1!=a2:
            return ("", f"Different argument types: a/{a1} -> b/{a2}")

    # The return-type has not changed
    if change.old.ident != change.new.ident:
        return ("", f"Different return type: a/{change.old.ident.type_spelling} -> b/{change.old.ident.type_spelling}")



    #print_info(f"{change.old.filepath}: {change.old.ident}")
    #for arg in change.old.arguments:
    #    print(f"\t{arg}")


    return (harness_path, "TODO")

