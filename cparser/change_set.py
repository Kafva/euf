from itertools import zip_longest

from clang import cindex
from git.diff import Diff
from git.repo.base import Repo

from cparser import CONFIG, DependencyFunction, CursorPair, \
        DependencyFunctionChange, SourceDiff, SourceFile, get_path_relative_to
from cparser.util import get_column_counts, print_err, print_info


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

    To automate harness generation we need to record argument types and return values for
    the functions that have changed. TODO: Determining which pointer arguments change
    would be very useful, we might be able to do this through analyzing the function body
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
        cursor_pairs: dict[str,CursorPair], root_dir:str, is_new: bool) -> None:

        if len(list(cursor.get_children())) == 0:
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
                        get_path_relative_to(str(child.location.file), root_dir)
                else:
                    cursor_pairs[key].old = child
                    cursor_pairs[key].old_path = \
                        get_path_relative_to(str(child.location.file), root_dir)

    def functions_differ(cursor_old: cindex.Cursor,
        cursor_new: cindex.Cursor) -> bool:
        '''
        Dependency functions are considered different at this stage if
        the cursors have a different number of nodes at any level or if the
        typing of their arguments differ
        '''
        for arg_old,arg_new in zip_longest(\
                cursor_old.get_arguments(), cursor_new.get_arguments()):
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

    extract_function_decls_to_pairs(cursor_old, cursor_pairs, old_root_dir, is_new=False)
    extract_function_decls_to_pairs(cursor_new, cursor_pairs, new_root_dir, is_new=True)

    # If the function pairs differ based on AST traversal,
    # add them to the list of changed_functions.
    # If the function prototypes differ, we can assume that an influential
    # change has occurred and we do not need to
    # perform a deeper SMT analysis
    for pair in cursor_pairs.values():
        if not pair.new:
            if CONFIG.VERBOSITY >= 3:
                print(f"Deleted: {pair.old_path} {pair.old.spelling}()")
            continue
        elif not pair.old:
            if CONFIG.VERBOSITY >= 3:
                print(f"New: {pair.new_path} {pair.new.spelling}()")
            continue

        cursor_old_fn = pair.old
        cursor_new_fn = pair.new

        function_change = DependencyFunctionChange.new_from_cursors(
                old_root_dir, new_root_dir,
                cursor_old_fn, cursor_new_fn
        )

        if functions_differ(cursor_old_fn, cursor_new_fn): # type: ignore
            if CONFIG.VERBOSITY >= 3:
                print(f"Differ: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")
            changed_functions.append(function_change)
        elif CONFIG.VERBOSITY >= 3:
            print(f"Same: a/{pair.new_path} b/{pair.old_path} {pair.new.spelling}()")

    return changed_functions

def get_transative_changes_from_file(source_file: SourceFile, dep_root_dir:str,
    changed_functions: list[DependencyFunctionChange]) -> dict[DependencyFunction,list[str]]:
    '''
    Go through the complete AST of the provided (new) file and save 
    any transative calls.

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
    encolsing functions perform these calls in the 
    transative_function_calls dict
    '''

    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():
        current_function = DependencyFunction.new_from_cursor(dep_root_dir, cursor)

    elif str(cursor.kind).endswith("CALL_EXPR") and \
        (dep_func := next(filter(lambda fn: \
        fn.new.ident.spelling == cursor.spelling, changed_functions), None \
    )):
        # Ensure that return type and arguments of the call
        # match the prototype in the change set
        called = DependencyFunction.new_from_cursor(dep_root_dir, cursor)

        if dep_func.new.eq(called) and \
           current_function.ident.spelling != cursor.spelling:
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

def add_rename_changes_based_on_blame(new_dep_repo: Repo, added_diff: list[Diff],
        dep_source_diffs: list[SourceDiff]) -> None:
    '''
    In some situations Git is not able to detect a rename across
    different commits, however the `git blame` output of added
    files can still show that certain "new" files are actually
    closer to rename operations.
    '''
    for added_file in added_diff:
        blame_output = new_dep_repo.git.blame("-f", added_file.a_path) # type: ignore

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

def log_changed_functions(changed_functions: list[DependencyFunctionChange], filename: str):
    if CONFIG.ENABLE_RESULT_LOG:
        with open(filename, mode='w', encoding='utf8') as f:
            f.write("direct_change;old_filepath;old_name;old_line;old_col;new_filepath;new_name;new_line;new_col\n")
            for change in changed_functions:
                f.write(f"{change.to_csv()}\n")

