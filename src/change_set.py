import os, traceback
from itertools import zip_longest

from clang import cindex
from git.diff import Diff
from git.exc import GitCommandError
from git.repo.base import Repo

from src.config import CONFIG
from src.types import DependencyFunction, CursorPair, \
    DependencyFunctionChange, IdentifierLocation, SourceDiff, SourceFile
from src.util import get_column_counts, print_info, print_err, time_end, time_start

def get_non_static(changed_functions:
 list[DependencyFunctionChange]) -> list[DependencyFunctionChange]:
    non_static_changes = []
    for c in changed_functions:
        if not c.old.ident.is_static and not c.new.ident.is_static:
            non_static_changes.append(c)
    return non_static_changes

def extract_function_decls_to_pairs(diff: SourceDiff, cursor: cindex.Cursor,
    cursor_pairs: dict[str,CursorPair], root_dir:str, is_new: bool) -> None:

    if len(list(cursor.get_children())) == 0 and CONFIG.VERBOSITY > 1:
        print_err(f"No data to parse for {cursor.spelling}")

    for child in cursor.get_children():
        if str(child.kind).endswith("FUNCTION_DECL") and \
            str(child.type.kind).endswith("FUNCTIONPROTO") and \
            child.is_definition() and \
            str(child.location.file).startswith(root_dir):
            # Note: A TU can #include other C-files, to properly trace
            # calls in the output we need to store these paths rather than
            # the path to the main file for each function
            # Any source file outside the root of the repository is not
            # processed (e.g. includes from /usr/include)

            # Note: the key in the dict uses the new and old filepath
            # to ensure that functions in renamed paths still end up in the same pair
            key = f"{diff.new_path}:{diff.old_path}:{child.spelling}"


            # Add the child to an existing pair or create a new one
            if not key in cursor_pairs:
                cursor_pairs[key] = CursorPair()

            if is_new:
                cursor_pairs[key].new = child
                cursor_pairs[key].new_path = \
                    str(child.location.file).removeprefix(root_dir).removeprefix("/")
            else:
                cursor_pairs[key].old = child
                cursor_pairs[key].old_path = \
                    str(child.location.file).removeprefix(root_dir).removeprefix("/")

def functions_differ(cursor_old: cindex.Cursor,
    cursor_new: cindex.Cursor) -> cindex.SourceLocation|None:
    '''
    Dependency functions are considered different at this stage if
    the cursors have a different number of nodes at any level or if the
    typing of their arguments differ

    For higher verbosity, we return the source location (in the old version) 
    where the versions diverged. This is useful for reasoning about FPs since
    functions which do not differ syntaxwise sometimes differ in their AST, e.g.
    when parameter types to functions change
    '''
    for arg_old,arg_new in zip_longest(\
      cursor_old.get_arguments(), cursor_new.get_arguments()):

        if not arg_old:
            return cursor_old.location
        if not arg_new:
            return arg_old.location
        if arg_old.kind != arg_new.kind:
            return arg_old.location

    for child_old,child_new in \
     zip_longest(cursor_old.get_children(), cursor_new.get_children()):

        if not child_old:
            return cursor_old.location
        if not child_new:
            return child_old.location
        if src_loc := functions_differ(child_old,child_new):
            return src_loc

def get_changed_functions_from_diff(diff: SourceDiff, new_root_dir: str,
    old_root_dir: str) -> list[DependencyFunctionChange]:
    '''
    Walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each function pair and exit as soon as any divergence occurs

    Processing nested function definitions would infer that the entire AST needs to be
    traversed, this could be unnecessary if this feature is not used in the code base
    
    The from_source() method also accepts content from arbitrary text streams,
    but this causes inconsistencies that produce an incomplete AST, we therefore need
    to read both versions directly from disk

    To automate harness generation we need to record argument types and return values for
    the functions that have changed. TODO: Determining which pointer arguments change
    would be very useful, we might be able to do this through analyzing the function body

    '''

    path_old = f"{old_root_dir}/{diff.old_path}"

    os.chdir(diff.old_compile_dir)
    tu_old = cindex.TranslationUnit.from_source(
            path_old,
            args = diff.old_compile_args
    )
    cursor_old: cindex.Cursor = tu_old.cursor

    path_new = f"{new_root_dir}/{diff.new_path}"

    os.chdir(diff.new_compile_dir)
    tu_new = cindex.TranslationUnit.from_source(
        path_new,
        args =  diff.new_compile_args
    )
    cursor_new: cindex.Cursor = tu_new.cursor

    print_diag_errors(path_old,tu_old)
    print_diag_errors(path_new,tu_new)

    changed_functions: list[DependencyFunctionChange] = list()
    cursor_pairs: dict[str,CursorPair]= {}

    extract_function_decls_to_pairs(diff, cursor_old, cursor_pairs, old_root_dir, is_new=False)
    extract_function_decls_to_pairs(diff, cursor_new, cursor_pairs, new_root_dir, is_new=True)

    # If the function pairs differ based on AST traversal,
    # add them to the list of changed_functions.
    # If the function prototypes differ, we can assume that an influential
    # change has occurred and we do not need to
    # perform a deeper SMT analysis
    for pair in cursor_pairs.values():

        if not pair.new:
            if CONFIG.VERBOSITY >= 5:
                print(f"Deleted: a/{pair.old_path} {pair.old.spelling}()")
            continue
        elif not pair.old:
            if CONFIG.VERBOSITY >= 5:
                print(f"New: b/{pair.new_path} {pair.new.spelling}()")
            continue

        cursor_old_fn = pair.old
        cursor_new_fn = pair.new


        function_change = DependencyFunctionChange.new_from_cursors(
                old_root_dir, new_root_dir,
                cursor_old_fn, cursor_new_fn
        )

        if type(src_loc := functions_differ(cursor_old_fn, cursor_new_fn)) == \
         cindex.SourceLocation:
            if CONFIG.VERBOSITY >= 5:
                print(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

            function_change.point_of_divergence = \
                IdentifierLocation.new_from_src_loc(src_loc) # type: ignore

            changed_functions.append(function_change)
        elif CONFIG.VERBOSITY >= 5:
            print(f"Same: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

    return changed_functions

def get_transative_changes_from_file(source_file: SourceFile, dep_root_dir:str,
    changed_functions: list[DependencyFunctionChange]) -> dict[DependencyFunction,list[str]]:
    '''
    Go through the complete AST of the provided (new) file and save 
    any transitive calls.

    If a changed function is called from the old version, and the call is removed
    in the new version, the function in question will have had a direct change and
    will already be in the change set.

    If a changed function is called from the new version but not the old version, 
    the function will similarly already be part of the change set. In these instances
    the callee will be considered affected by both a direct AND an indirect change.

    By enumerating changed function calls in the new version, we catch all indirect
    changes were both the old and new version call a function +
    instances were only the new version makes a call.

    key: 'enclosing_function'
    value: [ called_functions ]
    '''
    transative_function_calls: dict[DependencyFunction,list[str]] = {}

    translation_unit: cindex.TranslationUnit  = \
            cindex.TranslationUnit.from_source(
            source_file.new_path, args = source_file.new_compile_args
    )
    cursor: cindex.Cursor       = translation_unit.cursor

    find_transative_changes_in_tu(dep_root_dir, cursor,
        changed_functions, transative_function_calls, DependencyFunction.empty()
    )
    return transative_function_calls

def find_transative_changes_in_tu(dep_root_dir: str, cursor: cindex.Cursor,
    changed_functions: list[DependencyFunctionChange],
    transative_function_calls: dict[DependencyFunction,list[str]],
    current_function: DependencyFunction) -> None:
    '''
    Look for calls to functions in the change-set and record which
    enclosing functions perform these calls in the 
    transitive_function_calls dict
    '''

    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():
        current_function = DependencyFunction.new_from_cursor(dep_root_dir, cursor)

    elif str(cursor.kind).endswith("CALL_EXPR") and \
        (dep_func := next(filter(lambda fn: \
        fn.new.ident.location.name == cursor.spelling, changed_functions), None \
    )):
        # Ensure that return type and arguments of the call
        # match the prototype in the change set
        called = DependencyFunction.new_from_cursor(dep_root_dir, cursor)

        if dep_func.new.eq(called) and \
           current_function.ident.location.name != cursor.spelling:
            # If the enclosing function is calling itself we do not
            # record it as being 'indirectly affected'
            key = current_function
            if not key in transative_function_calls:
                transative_function_calls[key] = []

            transative_function_calls[key].append(
                f"{cursor.location.file}:{cursor.location.line}:" +
                f"{cursor.location.column}:{cursor.spelling}()"
            )

    for child in cursor.get_children():
        find_transative_changes_in_tu(dep_root_dir, child, changed_functions,
            transative_function_calls, current_function)

def add_rename_changes_based_on_blame(new_dep_path: str, added_diff: list[Diff],
        dep_source_diffs: list[SourceDiff]) -> None:
    '''
    In some situations Git is not able to detect a rename across
    different commits, however the `git blame` output of added
    files can still show that certain "new" files are actually
    closer to rename operations.
    '''
    if CONFIG.VERBOSITY >= 2:
        start = time_start("Looking for implicit 'RENAME' actions through blame...")

    for added_file in added_diff:
        try:
            blame_output = Repo(new_dep_path).git.blame("-f", added_file.a_path) # type: ignore
        except GitCommandError:
            traceback.print_exc()
            print_err("Git blame correlation failed")
            return

        # Create a list '[ (file_origin, count) ... ]' that describes how many 
        # lines originates from each file in the blame output
        file_origins = get_column_counts(blame_output, 1) # type: ignore

        # If the file origin dict only contains two entries and the distribution
        # is between 50/50 and RENAME_RATIO/(1-RENAME_RATIO) we assume that the file has been renamed
        if len(file_origins) == 2:

            total = file_origins[0][1] + file_origins[1][1]
            min_ratio = min(file_origins[0][1] / total, file_origins[1][1] / total)

            if .5 > min_ratio and min_ratio > CONFIG.RENAME_RATIO_LOW:
                # Create a new source diff object for the two files in question
                # provided that an entry does not already exist
                if file_origins[0][0] == added_file.a_path:
                    new_path = file_origins[0][0]
                    old_path = file_origins[1][0]
                else:
                    new_path = file_origins[1][0]
                    old_path = file_origins[0][0]

                assert( not any( d.new_path == new_path \
                        for d in dep_source_diffs)
                )

                if CONFIG.VERBOSITY >= 1:
                    print_info(f"Adding a/{old_path} -> b/{new_path} as a " + \
                            f"diff based on blame ratio: {round(min_ratio,3)}/{round(1-min_ratio,3)}")
                dep_source_diffs.append( SourceDiff(
                            new_path = new_path,
                            old_path = old_path,
                            new_compile_args = [],
                            old_compile_args = []
                ))
    if CONFIG.VERBOSITY >= 2:
        time_end("Git blame analysis done", start) # type: ignore

def log_changed_functions(changed_functions: list[DependencyFunctionChange], filename: str):
    if CONFIG.ENABLE_RESULT_LOG:
        with open(filename, mode='w', encoding='utf8') as f:
            f.write(f"direct_change;{IdentifierLocation.csv_header('old')};{IdentifierLocation.csv_header('new')}\n")
            for change in changed_functions:
                f.write(f"{change.to_csv()}\n")

def print_diag_errors(filepath:str, tu: cindex.TranslationUnit):
    if CONFIG.VERBOSITY >= 3:
        for d in tu.diagnostics:
            print_err(str(d))
    elif len(tu.diagnostics) > 0 and CONFIG.VERBOSITY > 1:
        # Header entries from compdb usually generate a lot of errors
        if not filepath.endswith(".h"):
            msgs = f", {len(tu.diagnostics)-1} more message(s)" \
                    if len(tu.diagnostics) > 1 else ''
            print_err(f"{str(tu.diagnostics[0])}" + msgs)



