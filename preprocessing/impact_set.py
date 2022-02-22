from clang import cindex
from base import DependencyFunction, ProjectInvocation, SourceFile

def get_call_sites_from_file(source_file: SourceFile,
    changed_functions: list[DependencyFunction]) -> list[ProjectInvocation]:
    '''
    Return a list of call sites in the provided source
    file for the functions in `changed_functions`
    '''
    call_sites = []

    translation_unit: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    find_call_sites_in_tu(source_file.new_path, cursor, changed_functions, call_sites)

    return call_sites


def find_call_sites_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: list[DependencyFunction], call_sites: list[ProjectInvocation]) -> None:
    '''
    Go through the complete AST of the provided file and save any sites
    where a changed function is called as an invocation
    '''
    if str(cursor.kind).endswith("CALL_EXPR") and \
            (func := next(filter(lambda fn: \
            fn.name == cursor.spelling, changed_functions), None \
    )):

        call_sites.append(ProjectInvocation(
            function = func,
            filepath = filepath,
            line = cursor.location.line,
            col  = cursor.location.column
        ))
    else:
        # We do not need to process children of a remote call
        for child in cursor.get_children():
            find_call_sites_in_tu(filepath, child, changed_functions, call_sites)
