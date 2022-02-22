from clang import cindex
from base import Function, Invocation, CLANG_INDEX, SourceFile

def get_call_sites_from_file(source_file: SourceFile,  changed_functions: list[Function]) -> list[Invocation]:
    call_sites = []

    tu: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.compile_args
    )
    cursor: cindex.Cursor       = tu.cursor

    find_call_sites_in_tu(source_file.new_path, cursor, changed_functions, call_sites)

    return call_sites


def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: list[Function], call_sites: list[Invocation]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an invocation
    '''
    if str(cursor.kind).endswith("CALL_EXPR") and \
            (fn := next(filter(lambda fn: \
            fn.name == cursor.spelling, changed_functions), None \
    )):

        call_sites.append(Invocation(
            function = fn,
            filepath = filepath,
            line = cursor.location.line,
            col  = cursor.location.column
        ))
    else:
        # We do not need to process children of a remote call
        for c in cursor.get_children():
            find_call_sites_in_tu(filepath, c, changed_functions, call_sites)

