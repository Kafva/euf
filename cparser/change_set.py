import logging
from itertools import zip_longest

from clang import cindex

from cparser import DependencyFunction, CursorPair, DependencyFunctionChange, SourceDiff, SourceFile

def get_changed_functions_from_diff(diff: SourceDiff, new_root_dir: str,
    old_root_dir: str) -> list[DependencyFunctionChange]:
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

    changed_functions: list[DependencyFunctionChange]       = list()
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

        function_change = DependencyFunctionChange.new_from_cursors(
                diff.old_path, diff.new_path,
                cursor_old_fn, cursor_new_fn
        )

        if functions_differ(cursor_old_fn, cursor_new_fn): # type: ignore
            logging.info(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")
            changed_functions.append(function_change)
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
    changed_functions: list[DependencyFunctionChange]) -> dict[DependencyFunction,list[str]]:
    '''
    Go through the complete AST of the provided (new) file and save 
    any transative calls
    
    key: 'enclosing_function'
    value: [ called_functions ]
    '''
    transative_function_calls: dict[DependencyFunction,list[str]] = {}

    translation_unit: cindex.TranslationUnit  = \
            cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.new_compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    find_transative_changes_in_tu(source_file.new_path, cursor,
        changed_functions, transative_function_calls, DependencyFunction.empty()
    )
    return transative_function_calls

def find_transative_changes_in_tu(filepath: str, cursor: cindex.Cursor,
    changed_functions: list[DependencyFunctionChange],
    transative_function_calls: dict[DependencyFunction,list[str]],
    current_function: DependencyFunction) -> None:
    '''
    Look for calls to functions in the change-set and record which
    encolsing functions perform these calls in the transative_function_calls dict
    '''

    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():

        current_function = DependencyFunction.new_from_cursor(filepath, cursor)

    elif str(cursor.kind).endswith("CALL_EXPR") and \
        (dep_func := next(filter(lambda fn: \
        fn.new.name == cursor.spelling, changed_functions), None \
    )):
        # Ensure that arguments and return value also match the changed entity
        # NOTE: This omits transative changes were function prototypes
        # have been changed.
        matching = True

        func_args_main_types = [ str(child.type.kind) \
                for child in cursor.get_arguments() ]

        if len(func_args_main_types) != len(dep_func.new.arguments):
            matching = False
        else:
            for fn_arg_dep, fn_arg_main_type in \
                    zip(dep_func.new.arguments, func_args_main_types):
                if fn_arg_dep.type != fn_arg_main_type:
                    matching = False
                    break

        if matching:
            key = current_function
            if not key in transative_function_calls:
                transative_function_calls[key] = []

            transative_function_calls[key].append(
            f"{cursor.spelling}():{cursor.location.line}:{cursor.location.column}"
            )

    for child in cursor.get_children():
        find_transative_changes_in_tu(filepath, child, changed_functions,
            transative_function_calls, current_function)
