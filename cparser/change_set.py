import logging
from itertools import zip_longest
from typing import Set

from clang import cindex

from cparser import DependencyFunction, CursorPair, SourceDiff, SourceFile

def get_changed_functions_from_diff(diff: SourceDiff, new_root_dir: str,
    old_root_dir: str) -> Set[DependencyFunction]:
    '''
    Walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each funcion pair and exit as soon as any divergence occurs

    Processing nested function definitions would infer that the entire AST needs to be
    traveresed, this could be unnecessary if this feature is not used in the code base
    
    The from_source() method also accepts content from arbitrary text streams,
    but this causes inconsitencies that produce an incomplete AST, we therefore need
    to read both versions directly from disk
    '''

    tu_old = cindex.TranslationUnit.from_source(
            f"{old_root_dir}/{diff.old_path}",
            args = diff.old_compile_args
    )
    cursor_old: cindex.Cursor = tu_old.cursor

    tu_new = cindex.TranslationUnit.from_source(
        f"{new_root_dir}/{diff.new_path}",
        args = diff.new_compile_args
    )
    cursor_new: cindex.Cursor = tu_new.cursor

    changed_functions: Set[DependencyFunction]       = set()
    cursor_pairs: dict[str,CursorPair]      = {}

    def extract_function_decls_to_pairs(cursor: cindex.Cursor,
        cursor_pairs: dict[str,CursorPair], is_new: bool) -> None:
        for child in cursor.get_children():

            if str(child.kind).endswith("FUNCTION_DECL") and child.is_definition():
                # Note: the key in the dict uses the new and old filepath
                # to ensure that functions in renamed paths still end up in the same pair
                key = f"{diff.new_path}:{diff.old_path}:{child.spelling}"

                # Add the child to an existing pair or create a new one
                if not key in cursor_pairs:
                    cursor_pairs[key] = CursorPair()

                cursor_pairs[key].add(child, diff, is_new)

    def functions_differ(cursor_old: cindex.Cursor,
        cursor_new: cindex.Cursor) -> bool:
        '''
        Dependency functions are considered different at this stage if
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
            logging.info(f"Deleted: {pair.old_path} {pair.old.spelling}()")
            continue
        elif not pair.old:
            logging.info(f"New: {pair.new_path} {pair.new.spelling}()")
            continue

        cursor_old_fn = pair.old
        cursor_new_fn = pair.new

        function = DependencyFunction.new_from_cursor(diff.old_path, cursor_old_fn)

        if functions_differ(cursor_old_fn, cursor_new_fn): # type: ignore
            logging.info(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")
            changed_functions.add(function)
        else:
            logging.info(f"Same: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

    return changed_functions

def dump_top_level_decls(cursor: cindex.Cursor, recurse: bool = False) -> None:
    for child in cursor.get_children():
        if recurse:
            print(f"\033[34m{child.spelling}\033[0m")
            dump_children(child,0)
        elif child.spelling != "":
            print(child.spelling)

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_transative_changes_from_file(source_file: SourceFile,
    changed_functions: Set[DependencyFunction]) -> Set[DependencyFunction]:
    '''
    Go through the complete AST of the provided file and add any functions
    which invoke a function from the changed set to the transative change set
    '''
    transative_functions = set()

    translation_unit: cindex.TranslationUnit  = \
            cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.new_compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    find_transative_changes_in_tu(source_file.new_path, cursor,
        changed_functions, transative_functions, DependencyFunction.empty()
    )
    return transative_functions

def find_transative_changes_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: Set[DependencyFunction],
    transative_functions: Set[DependencyFunction],
    current_function: DependencyFunction) -> None:

    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():

        current_function = DependencyFunction.new_from_cursor(filepath, cursor)

    elif str(cursor.kind).endswith("CALL_EXPR") and \
        (dep_func := next(filter(lambda fn: \
        fn.name == cursor.spelling, changed_functions), None \
    )):
        # Ensure that arguments also match the changed entity
        # TODO: This omits transative changes were function prototypes
        # have been changed.
        matching_args = True

        func_args_main_types = [ str(child.type.kind) \
                for child in cursor.get_arguments() ]

        if len(func_args_main_types) != len(dep_func.arguments):
            matching_args = False
        else:
            for fn_arg_dep, fn_arg_main_type in \
                    zip(dep_func.arguments, func_args_main_types):
                if fn_arg_dep.type != fn_arg_main_type:
                    matching_args = False
                    break

        if matching_args:
            current_function.invokes_changed_functions.append(
            f"{filepath}:{cursor.displayname}:{cursor.location.line}:{cursor.location.column}"
            )

            # If there already exists an entry for the current function in
            # the set, remove it, and add the new entry
            # TODO: Very ugly hack
            if current_function in transative_functions:
                transative_functions.remove(current_function)

            transative_functions.add(current_function)

    for child in cursor.get_children():
        find_transative_changes_in_tu(filepath, child, changed_functions,
            transative_functions, current_function)
