from clang import cindex
from base import Function, Invocation

def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_function_names: list[str],
    call_sites: list[Function]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called
    '''
    if str(cursor.kind).endswith("CALL_EXPR") and \
        cursor.spelling in changed_function_names:
        # TODO: We need to add the actual path of the current function
        call_sites.append(cursor.spelling)

    for c in cursor.get_children():
        find_call_sites_in_tu(filepath, c, changed_function_names, call_sites)

