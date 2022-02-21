from clang import cindex

def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_function_names: list[str],
    call_sites: dict[str,list[str]]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called
    '''

    if str(cursor.kind).endswith("CALL_EXPR") and \
        cursor.spelling in changed_function_names:

        if filepath in call_sites:
            call_sites[filepath] = [ cursor.spelling ]
        else:
            call_sites[filepath].append(cursor.spelling)

    for c in cursor.get_children():
        find_call_sites_in_tu(filepath, c, changed_function_names, call_sites)

