from logging import info
from itertools import zip_longest

from clang import cindex

from base import DependencyFunction, CursorPair, SourceDiff

def get_changed_functions_from_diff(diff: SourceDiff, root_dir: str) -> list[DependencyFunction]:
    '''
    Walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each funcion pair and exit as soon as any divergence occurs

    Processing nested function definitions would infer that the entire AST needs to be
    traveresed, this could be unnecessary if this feature is not used in the code base
    
    The from_source() method accepts content from arbitrary text streams,
    allowing us to analyze the old version of each file
    '''

    tu_old = cindex.TranslationUnit.from_source(
            f"{root_dir}/{diff.old_path}",
            unsaved_files=[ (f"{root_dir}/{diff.old_path}", diff.old_content) ],
            args = diff.compile_args
    )
    cursor_old: cindex.Cursor = tu_old.cursor

    tu_new = cindex.TranslationUnit.from_source(
        f"{root_dir}/{diff.new_path}",
        args = diff.compile_args
    )
    cursor_new: cindex.Cursor = tu_new.cursor

    changed_functions: list[DependencyFunction]       = []
    cursor_pairs: dict[str,CursorPair]      = {}

    def extract_function_decls_to_pairs(cursor: cindex.Cursor,
        cursor_pairs: dict[str,CursorPair], is_new: bool) -> None:
        for child in cursor.get_children():

            if str(child.kind).endswith("FUNCTION_DECL") and child.is_definition():
                # Note: the key in the dict _always_ uses the new filepath
                # to ensure that functions in renamed paths still end up in the same pair
                # TODO: Handle edge case when filenames are switched
                #   foo.c     -> src/bar.c (already exists)
                #   src/bar.c -> foo.c
                key = f"{diff.new_path}:{child.spelling}"

                # Add the child to an existing pair or create a new one
                if not key in cursor_pairs:
                    cursor_pairs[key] = CursorPair()

                cursor_pairs[key].add(child, diff, is_new)

    def functions_differ(cursor_old: cindex.Cursor,
        cursor_new: cindex.Cursor) -> bool:
        '''
        DependencyFunctions are considered different at this stage if
        the cursors have a different number of nodes at any level or if the
        typing of their arguments differ
        '''
        for arg_old,arg_new in zip_longest(cursor_old.get_arguments(), cursor_new.get_arguments()):
            if not arg_old or not arg_new:
                return True
            if arg_old.kind != arg_new.kind:
                return True

        for child_old,child_new in \
            zip_longest(cursor_old.get_children(), cursor_new.get_children()):
            if not child_old or not child_new:
                return True
            if functions_differ(child_old,child_new):
                return True

        return False

    extract_function_decls_to_pairs(cursor_old, cursor_pairs,  is_new=False)
    extract_function_decls_to_pairs(cursor_new, cursor_pairs,  is_new=True)

    # If the function pairs differ based on AST traversal,
    # add them to the list of changed_functions.
    # If the function prototypes differ, we can assume that an influential
    # change has occurred and we do not need to
    # perform a deeper SMT analysis
    for pair in cursor_pairs.values():
        if not pair.new:
            info(f"Deleted: {pair.old_path} {pair.old.spelling}()")
            continue
        elif not pair.old:
            info(f"New: {pair.new_path} {pair.new.spelling}()")
            continue

        cursor_old_fn = pair.old
        cursor_new_fn = pair.new

        function = DependencyFunction(
            filepath    = diff.new_path,
            displayname = cursor_old_fn.displayname,
            name        = cursor_old_fn.spelling,
            return_type = cursor_old_fn.type.get_result().kind,
            arguments   = [ (t.kind,n.spelling) for t,n in \
                    zip(cursor_old_fn.type.argument_types(), \
                    cursor_old_fn.get_arguments()) ]
        )

        if functions_differ(cursor_old_fn, cursor_new_fn): # type: ignore
            info(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")
            changed_functions.append(function)
        else:
            info(f"Same: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

    return changed_functions

def dump_top_level_decls(diff: SourceDiff, root_dir: str) -> None:
    tu_old = cindex.TranslationUnit.from_source(
            f"{root_dir}/{diff.old_path}",
            unsaved_files=[ (f"{root_dir}/{diff.old_path}", diff.old_content) ],
            args = diff.compile_args
    )
    cursor: cindex.Cursor = tu_old.cursor

    for child in cursor.get_children():
        if child.spelling != "":
            print(child.spelling)

