from cparser import DependencyFunctionChange
from cparser.util import print_info

def create_harness(change: DependencyFunctionChange) -> str:
    '''
    Firstly, we need to know basic information about the function we are
    generating a harness for:
        full prototype string (forward decl)
        name
        args
        return type
    All of this information has been saved in the `change` object during
    the AST diffing stage
    '''
    harness_path = ""
    print_info(f"{change.old.filepath}: {change.old.ident}")


    return harness_path

