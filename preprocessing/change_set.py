from itertools import zip_longest
from clang import cindex
from base import Function, debug_print, CursorContext


def get_changed_functions(cursor_old: cindex.Cursor, cursor_new: cindex.Cursor,
        filepath: str, dump: bool = False) -> list[Function]:
    '''
    As a starting point we can walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each funcion pair and exit as soon as any divergence occurs

    TODO: Processing nested function definitions would infer that the entire AST needs to be
    traveresed, this could be unnecessary if this feature is not used in the code base
    '''

    changed_functions: list[Function] = []
    cursor_pairs = {}

    def dump_print(fmt: str) -> None:
        if dump: debug_print(fmt)

    def extract_pairs(cursor: cindex.Cursor, cursor_pairs: dict, key: CursorContext) -> None:
        for c in cursor.get_children():
            if str(c.kind).endswith("FUNCTION_DECL") and c.is_definition():

                if c.displayname in cursor_pairs:
                    cursor_pairs[c.displayname][key] = c
                else:
                    cursor_pairs[c.displayname]      = { key: c }

    def functions_differ(cursor_old: cindex.Cursor, cursor_new: cindex.Cursor) -> bool:
        ''' 
        Functions are considered different at this stage if
        the cursors have a different number of nodes at any level or if the
        typing of their arguments differ
        '''
        for t1,t2 in zip_longest(cursor_old.get_arguments(), cursor_new.get_arguments()):
            if not t1 or not t2:
                return True
            elif t1.kind != t2.kind:
                return True

        for c1,c2 in zip_longest(cursor_old.get_children(), cursor_new.get_children()):
            if not c1 or not c2:
                return True
            elif functions_differ(c1,c2):
                return True

        return False

    extract_pairs(cursor_old, cursor_pairs, CursorContext.CURRENT)
    extract_pairs(cursor_new, cursor_pairs,  CursorContext.NEW)

    for key in cursor_pairs:
        # If the function pairs differ based on AST traversal, 
        # add them to the list of changed_functions. 
        # If the function prototypes differ, we can assume that an influential 
        # change has occurred and we do not need to 
        # perform a deeper SMT analysis

        if not CursorContext.NEW in cursor_pairs[key]:
            dump_print(f"Deleted: {key}")
            continue
        elif not CursorContext.CURRENT in cursor_pairs[key]:
            dump_print(f"New: {key}")
            continue

        cursor_old = cursor_pairs[key][CursorContext.CURRENT]
        cursor_new = cursor_pairs[key][CursorContext.NEW]

        function = Function(
            filepath    = filepath,
            displayname = cursor_old.displayname,
            name        = cursor_old.spelling,
            return_type = cursor_old.type.get_result().kind,
            arguments   = [ (t.kind,n.spelling) for t,n in \
                    zip(cursor_old.type.argument_types(), \
                    cursor_old.get_arguments()) ]
        )

        if functions_differ(cursor_old, cursor_new):
            dump_print(f"Differ: {key}")
            changed_functions.append(function)
        else:
            dump_print(f"Same: {key}")


    return changed_functions

def dump_functions_in_tu(cursor: cindex.Cursor) -> None:
    '''
    By inspecting the AST we can determine what tokens are function declerations
    https://libclang.readthedocs.io/en/latest/index.html#clang.cindex.TranslationUnit.from_source
    '''
    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():

        print(f"{cursor.type.get_result().spelling} {cursor.spelling} (");

        for t,n in zip(cursor.type.argument_types(), cursor.get_arguments()):
                print(f"\t{t.spelling} {n.spelling}")
        print(")")

    for c in cursor.get_children():
        dump_functions_in_tu(c)

