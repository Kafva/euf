from itertools import zip_longest
from clang import cindex
from base import Function, CursorPair, IDX
from logging import debug
from git import Diff


def get_changed_functions_from_diff(diff: Diff, root_dir: str) -> list[Function]:
    '''
    The from_source() method accepts content from arbitrary text streams,
     allowing us to analyze the old version of each file
    '''
    tu_old = cindex.TranslationUnit.from_source(
            f"{root_dir}/{diff.b_path}",
            unsaved_files=[ (f"{root_dir}/{diff.b_path}", diff.b_blob.data_stream) ],
            index=IDX
    )
    cursor_old: cindex.Cursor = tu_old.cursor

    tu_new = cindex.TranslationUnit.from_source(f"{root_dir}/{diff.a_path}", index=IDX)
    cursor_new: cindex.Cursor = tu_new.cursor


    '''
    As a starting point we can walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each funcion pair and exit as soon as any divergence occurs

    Processing nested function definitions would infer that the entire AST needs to be
    traveresed, this could be unnecessary if this feature is not used in the code base
    '''

    changed_functions: list[Function]       = []
    cursor_pairs: dict[str,CursorPair]      = {}  # 'diff.a_path:funcname' -> (new: cursor, old: cursor)

    def extract_function_decls_to_pairs(cursor: cindex.Cursor, cursor_pairs: dict[str,CursorPair], is_new: bool) -> None:
        for c in cursor.get_children():

            if str(c.kind).endswith("FUNCTION_DECL") and c.is_definition():

                key = f"{diff.a_path}:{c.spelling}"

                #print(key, c.spelling, c.kind, c.is_definition(), "new" if is_new else "old")

                if not key in cursor_pairs:
                    cursor_pairs[key] = CursorPair()

                cursor_pairs[key].add(c, is_new)

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

    extract_function_decls_to_pairs(cursor_old, cursor_pairs,  is_new=False)
    extract_function_decls_to_pairs(cursor_new, cursor_pairs,  is_new=True)

    # If the function pairs differ based on AST traversal, 
    # add them to the list of changed_functions. 
    # If the function prototypes differ, we can assume that an influential 
    # change has occurred and we do not need to 
    # perform a deeper SMT analysis
    for key in cursor_pairs:
        if not cursor_pairs[key].new:
            debug(f"Deleted: {key}")
            continue
        elif not cursor_pairs[key].old:
            debug(f"New: {key}")
            continue

        cursor_old_fn = cursor_pairs[key].old
        cursor_new_fn = cursor_pairs[key].new

        function = Function(
            filepath    = diff.a_path,
            displayname = cursor_old_fn.displayname,
            name        = cursor_old_fn.spelling,
            return_type = cursor_old_fn.type.get_result().kind,
            arguments   = [ (t.kind,n.spelling) for t,n in \
                    zip(cursor_old_fn.type.argument_types(), \
                    cursor_old_fn.get_arguments()) ]
        )

        if functions_differ(cursor_old_fn, cursor_new_fn):
            debug(f"Differ: {key}")
            changed_functions.append(function)
        else:
            debug(f"Same: {key}")

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

