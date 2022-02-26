from itertools import zip_longest
from logging import info
from typing import Set

from clang import cindex

from base import DependencyArgument, DependencyFunction, CursorPair, SourceDiff

def get_changed_functions_from_diff(diff: SourceDiff, new_root_dir: str, old_root_dir: str) -> Set[DependencyFunction]:
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
            info(f"Deleted: {pair.old_path} {pair.old.spelling}()")
            continue
        elif not pair.old:
            info(f"New: {pair.new_path} {pair.new.spelling}()")
            continue

        cursor_old_fn = pair.old
        cursor_new_fn = pair.new

        function = DependencyFunction(
            filepath    = diff.old_path,
            displayname = cursor_old_fn.displayname,
            name        = cursor_old_fn.spelling,
            return_type = str(cursor_old_fn.type.get_result().kind),
            arguments   = [ DependencyArgument( \
                    type = str(n.type.kind), \
                    spelling = str(n.spelling) \
                 ) for n in cursor_old_fn.get_arguments() ],
            line = cursor_old_fn.location.line,
            col = cursor_old_fn.location.column
        )

        if functions_differ(cursor_old_fn, cursor_new_fn): # type: ignore
            info(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")
            changed_functions.add(function)
        else:
            info(f"Same: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

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

#def find_transative_calls_from_cursor(filepath: str, cursor: cindex.Cursor,
#        changed_functions: Set[DependencyFunction] ) -> None:
#    '''
#    Go through the complete AST of the provided cursor and save any sites
#    where a changed function is called
#
#    Directly changed      [dep.a() dep.b()]
#     1. dep.c() calls:    dep.a()
#     2. dep.e() calls:    dep.c()
#     3. dep.d() calls:    dep.e(), dep.b()
#      ...
#    Every changed function (directly or transativly) will be added to the changed_functions set
#    we can identify the direct changes from the fact that they lack a value for the
#    'invokes_changed_function' attribute
#
#    dep.d() -> dep.e() -> dep.c() -> dep.a()
#
#    '''
#
#    #if str(cursor.kind).endswith("CALL_EXPR") and \
#    #    (dep_func := next(filter(lambda fn: \
#    #    fn.name == cursor.spelling, changed_functions), None \
#    #)):
#
#    #    # We haft to verify that the called function has the expected parameters,
#    #    # since there could be a local function with the same name
#    #    # TODO: identify if our version of the function is included in the main file being analyzed
#    #    # otherwise the error could be a FP
#    #    matching_args = True
#
#    #    func_args_main_types = [ str(child.type.kind) for child in cursor.get_arguments() ]
#
#    #    if len(func_args_main_types) != len(dep_func.arguments):
#    #        matching_args = False
#    #    else:
#    #        for fn_arg_dep, fn_arg_main_type in zip(dep_func.arguments, func_args_main_types):
#
#    #            if fn_arg_dep.type != fn_arg_main_type:
#    #                matching_args = False
#    #                break
#
#    #    invocation = ProjectInvocation(
#    #            function = dep_func,
#    #            filepath = filepath,
#    #            line = cursor.location.line,
#    #            col  = cursor.location.column
#    #    )
#
#    #    if matching_args:
#    #        call_sites.append(invocation)
#    #    else:
#    #        print_err(f"Potentially inconsistent parameters for {invocation}:" +
#    #        f"\n  Prototype: {dep_func.displayname}\n  Invocation: {cursor.spelling}(" +
#    #        ", ".join(func_args_main_types) + ")"
#    #        )
#    #else:
#    #    # We do not need to process children of a remote call
#    #    for child in cursor.get_children():
#    #        find_call_sites_in_tu(filepath, child, changed_functions, call_sites)
#
#