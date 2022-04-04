from cparser import DependencyFunctionChange

def create_harness(change: DependencyFunctionChange) -> str:
    '''
    Firstly, we need to know basic information about the function we are
    generating a harness for:
        
        full prototype string (forward decl)
        name
        args
        return type
    '''
    harness_path = ""
    print(change, change.old.displayname)


    return harness_path

