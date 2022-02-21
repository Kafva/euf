from clang import cindex
from base import Function, Invocation

def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_function_names: list[str], call_sites: list[Invocation]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called
    '''

    if str(cursor.kind).endswith("CALL_EXPR") and \
        cursor.spelling in changed_function_names:
        # TODO: We need to add the actual path of the current function

        call_sites.append(cursor.spelling)
        #call_sites.append( Invocation(
        #    function = Function(
        #        filepath    = "TODO",
        #        displayname = cursor.displayname,
        #        name        = cursor.spelling,
        #        return_type = cursor.type.get_result().kind,
        #        arguments   = [ (t.kind,n.spelling) for t,n in \
        #                zip(cursor.type.argument_types(), \
        #                cursor.get_arguments()) ]
        #    ),
        #    filepath = filepath,
        #    location = cursor.location
        #))

    for c in cursor.get_children():
        find_call_sites_in_tu(filepath, c, changed_function_names, call_sites)

