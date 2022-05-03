import os, traceback
from posixpath import abspath
from itertools import zip_longest

from clang import cindex
from git.diff import Diff
from git.exc import GitCommandError
from git.repo.base import Repo

from src.config import CONFIG
from src.fmt import fmt_location
from src.types import DependencyFunction, CursorPair, \
    DependencyFunctionChange, IdentifierLocation, SourceDiff, SourceFile
from src.util import get_column_counts, git_dir, \
        git_relative_path, print_info, print_err, \
        shorten_path_fields, time_end, time_start

def functions_match(match: DependencyFunction, other: DependencyFunction) \
 -> bool:
    '''
    Ensure that the arguments and return value of the provided function
    match that of the current function object. Does not check the filepath
    '''
    match_str = fmt_location(match.ident.location)
    other_str = fmt_location(other.ident.location)

    if (err := match.ident.eq_report(other.ident, return_value=True, check_function=True)) != "":
        print(err)
        print(f"definition: {match_str}\ncall: {other_str}\n")
        return False

    for self_arg,other_arg in zip(match.arguments,other.arguments):
        if (err := self_arg.eq_report(other_arg, return_value=False, check_function=False)) != "":
            print(err)
            print(f"definition: {match_str}\ncall: {other_str}\n")
            return False

    return True

def get_non_static(changed_functions:
 list[DependencyFunctionChange]) -> list[DependencyFunctionChange]:
    non_static_changes = []
    for c in changed_functions:
        if not c.old.ident.is_static and not c.new.ident.is_static:
            non_static_changes.append(c)
    return non_static_changes

def extract_function_decls_to_pairs(diff: SourceDiff, cursor: cindex.Cursor,
 cursor_pairs: dict[str,CursorPair], is_new: bool) -> None:
    if len(list(cursor.get_children())) == 0 and CONFIG.VERBOSITY > 1:
        print_err(f"No data to parse for {cursor.spelling}")

    for child in cursor.get_children():

        filepath = str(child.location.file)

        # Ensure that the filepath is an abspath
        if not filepath.startswith("/"):
            filepath = f"{diff.compile_dir_new}/{filepath}" if is_new \
                    else f"{diff.compile_dir_old}/{filepath}"
            filepath = abspath(filepath)

        if str(child.kind).endswith("FUNCTION_DECL") and \
            str(child.type.kind).endswith("FUNCTIONPROTO") and \
            child.is_definition() and \
            filepath.startswith(git_dir(new=is_new)):
            # Note: A TU can #include other C-files, to properly trace
            # calls in the output we need to store these paths rather than
            # the path to the main file for each function
            # Any source file outside the root of the repository is not
            # processed (e.g. includes from /usr/include)

            # Note: the key in the dict uses the new and old filepath
            # to ensure that functions in renamed paths still end up in the same pair
            key = f"{diff.filepath_new}:{diff.filepath_old}:{child.spelling}"


            # Add the child to an existing pair or create a new one
            if not key in cursor_pairs:
                cursor_pairs[key] = CursorPair()

            if is_new:
                cursor_pairs[key].new = child
                cursor_pairs[key].filepath_new = filepath
            else:
                cursor_pairs[key].old = child
                cursor_pairs[key].filepath_old = filepath

def functions_differ(cursor_old: cindex.Cursor, cursor_new: cindex.Cursor) \
 -> cindex.SourceLocation|None:
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

def get_changed_functions_from_diff(diff: SourceDiff) \
 -> list[DependencyFunctionChange]:
    '''
    Walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change

    1. Save the cursors for each top-level function in both versions
    2. Walk both cursors in parallel for each function pair and exit 
    as soon as any divergence occurs

    The from_source() method also accepts content from arbitrary text streams,
    but this produce an incomplete AST, we therefore need to read 
    both versions directly from disk
    '''
    try:
        # We need to be in the correct directory for headers to
        # be included correctly
        os.chdir(diff.compile_dir_old)
        tu_old = cindex.TranslationUnit.from_source(
                diff.filepath_old,
                args = diff.compile_args_old
        )
        cursor_old: cindex.Cursor = tu_old.cursor
    except cindex.TranslationUnitLoadError:
        print_err(f"Failed to load TU: {diff.filepath_old}")
        return []

    try:
        os.chdir(diff.compile_dir_new)
        tu_new = cindex.TranslationUnit.from_source(
            diff.filepath_new,
            args =  diff.compile_args_new
        )
        cursor_new: cindex.Cursor = tu_new.cursor
    except cindex.TranslationUnitLoadError:
        print_err(f"Failed to load TU: {diff.filepath_new}")
        return []

    git_rel_path_old = git_relative_path(diff.filepath_old)
    git_rel_path_new = git_relative_path(diff.filepath_new)

    print_diag_errors(git_rel_path_old,tu_old)
    print_diag_errors(git_rel_path_new,tu_new)

    changed_functions: list[DependencyFunctionChange] = list()
    cursor_pairs: dict[str,CursorPair]= {}

    extract_function_decls_to_pairs(diff, cursor_old, cursor_pairs,is_new=False)
    extract_function_decls_to_pairs(diff, cursor_new, cursor_pairs,is_new=True)

    # If the function pairs differ based on AST traversal,
    # add them to the list of changed_functions.
    for pair in cursor_pairs.values():
        if not pair.new:
            if CONFIG.VERBOSITY >= 5:
                print(f"Deleted: a/{git_rel_path_old} {pair.old.spelling}()")
            continue
        elif not pair.old:
            if CONFIG.VERBOSITY >= 5:
                print(f"New: b/{git_rel_path_new} {pair.new.spelling}()")
            continue

        # We need to pass the filepaths explicitly in case the path
        # from the internal cursor is not an abspath
        function_change = DependencyFunctionChange.new_from_cursors(
                cursor_old = pair.old,
                cursor_new = pair.new,
                filepath_old = pair.filepath_old,
                filepath_new = pair.filepath_new
        )
        src_loc = functions_differ(pair.old, pair.new)

        if type(src_loc) == cindex.SourceLocation:
            if CONFIG.VERBOSITY >= 5:
                print(f"Differ: a/{git_rel_path_old} b/{git_rel_path_new}" + \
                        f" {pair.new.spelling}()")

            filepath = str(src_loc.file) # type: ignore

            # Ensure that the filepath is an abspath
            # The divergence is always given relative to the old version
            if not filepath.startswith("/"):
                filepath = f"{diff.compile_dir_old}/{filepath}"
                filepath = abspath(filepath)

            function_change.point_of_divergence = \
                IdentifierLocation.new_from_src_loc(src_loc,filepath=filepath) # type: ignore

            changed_functions.append(function_change)

        elif CONFIG.VERBOSITY >= 5:
            print(f"Same: a/{git_rel_path_old} b/{git_rel_path_new}" + \
                    f" {pair.new.spelling}()")

    return changed_functions

def get_transative_changes_from_file(source_file: SourceFile,
 changed_functions: list[DependencyFunctionChange]) \
 -> dict[DependencyFunction,list[str]]:
    '''
    Go through the complete AST of the provided (new) file and save 
    any transitive calls.

    If a changed function is called from the old version, 
    and the call is removed in the new version, the function in 
    question will have had a direct change and will already be in 
    the change set.

    If a changed function is called from the new version but not 
    the old version, the function will similarly already be part of the 
    change set. In these instances the callee will be considered affected 
    by both a direct AND an indirect change.

    By enumerating changed function calls in the new version, we catch 
    all indirect changes where both the old and new version call a function +
    instances were only the new version makes a call.
    '''
    # key: 'enclosing_function'
    # value: [ called_functions ]
    transative_function_calls: dict[DependencyFunction,list[str]] = {}

    os.chdir(source_file.compile_dir_new)
    translation_unit = cindex.TranslationUnit.from_source(
            source_file.filepath_new,
            args = source_file.compile_args_new
    )
    cursor = translation_unit.cursor

    find_transative_changes_in_tu(cursor,
        source_file.compile_dir_new, changed_functions,
        transative_function_calls, DependencyFunction.empty()
    )
    return transative_function_calls

def find_transative_changes_in_tu(cursor: cindex.Cursor,
 compile_dir: str, changed_functions: list[DependencyFunctionChange],
 transative_function_calls: dict[DependencyFunction,list[str]],
 current_function: DependencyFunction) -> None:
    '''
    Look for calls to functions in the change-set and record which
    enclosing functions perform these calls in the 
    transitive_function_calls dict
    '''
    change_matching_current = next(filter(lambda fn: \
        fn.new.ident.location.name == cursor.spelling, \
        changed_functions), None \
    )

    # If a file location is not given as an absolute path
    # we prepend the directory of the current cursor
    filepath = str(cursor.location.file)
    if not filepath.startswith("/"):
        filepath = f"{compile_dir}/{filepath}"
        filepath = abspath(filepath)

    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():
        current_function = \
            DependencyFunction.new_from_cursor(cursor, filepath=filepath)

    elif str(cursor.kind).endswith("CALL_EXPR") and \
     change_matching_current != None:

        called = DependencyFunction.new_from_cursor(cursor, filepath=filepath)

        # Ensure that return type and arguments of the call
        # match the prototype in the change set
        if functions_match(change_matching_current.new, called) and \
          current_function.ident.location.name != cursor.spelling:
            # If the enclosing function is calling itself we do not
            # record it as being 'indirectly affected'
            key = current_function
            if not key in transative_function_calls:
                transative_function_calls[key] = []

            transative_function_calls[key].append(
                fmt_location(called.ident.location)
            )

    for child in cursor.get_children():
        find_transative_changes_in_tu(child, compile_dir, changed_functions,
            transative_function_calls, current_function)

def add_rename_changes_based_on_blame(
 added_diff: list[Diff],
 dep_source_diffs: list[SourceDiff],
 dep_db_old: cindex.CompilationDatabase,
 dep_db_new: cindex.CompilationDatabase) -> None:
    '''
    In some situations Git is not able to detect a rename across
    different commits, however the `git blame` output of added
    files can still show that certain "new" files are actually
    closer to rename operations.
    '''
    if CONFIG.VERBOSITY >= 2:
        start = \
            time_start("Looking for implicit 'RENAME' actions through blame...")

    for added_file in added_diff:
        try:
            blame_output = Repo(git_dir(new=True)).git. \
                    blame("-f", added_file.a_path) # type: ignore
        except GitCommandError:
            traceback.print_exc()
            print_err("Git blame correlation failed")
            return

        # Create a list '[ (file_origin, count) ... ]' that describes how many 
        # lines originates from each file in the blame output
        file_origins = get_column_counts(blame_output, 1) # type: ignore

        # If the file origin dict only contains two entries and the distribution
        # is between 50/50 and RENAME_RATIO/(1-RENAME_RATIO) 
        # we assume that the file has been renamed
        if len(file_origins) == 2:

            total = file_origins[0][1] + file_origins[1][1]
            min_ratio = min(file_origins[0][1] / total, file_origins[1][1] /
                                                                          total)

            if .5 > min_ratio and min_ratio > CONFIG.RENAME_RATIO_LOW:
                # Create a new source diff object for the two files in question
                # provided that an entry does not already exist
                if file_origins[0][0] == added_file.a_path:
                    filepath_origin_new = file_origins[0][0]
                    filepath_origin_old = file_origins[1][0]
                else:
                    filepath_origin_new = file_origins[1][0]
                    filepath_origin_old = file_origins[0][0]

                assert( not any( git_relative_path(d.filepath_new) \
                        == filepath_origin_new \
                        for d in dep_source_diffs)
                )

                if CONFIG.VERBOSITY >= 1:
                    print_info(f"Adding a/{filepath_origin_old} -> " + \
                                      f"b/{filepath_origin_new} as a " + \
                            f"diff based on blame ratio: " + \
                            f"{round(min_ratio,3)}/{round(1-min_ratio,3)}")

                source_diff = SourceDiff.new(
                          filepath_old = f"{git_dir(new=False)}/{filepath_origin_old}",
                          ccdb_old = dep_db_old,
                          filepath_new = f"{git_dir(new=True)}/{filepath_origin_new}",
                          ccdb_new = dep_db_new
                        )
                dep_source_diffs.append(source_diff)

    if CONFIG.VERBOSITY >= 2:
        time_end("Git blame analysis done", start) # type: ignore

def log_changed_functions(changed_functions: list[DependencyFunctionChange],
 filename: str):
    if CONFIG.ENABLE_RESULT_LOG:
        with open(filename, mode='w', encoding='utf8') as f:
            f.write(f"direct_change;{IdentifierLocation.csv_header('old')};{IdentifierLocation.csv_header('new')}\n")
            for change in changed_functions:
                f.write(f"{shorten_path_fields(change.to_csv())}\n")

def print_diag_errors(filepath:str, tu: cindex.TranslationUnit):
    if CONFIG.VERBOSITY >= 3:
        for d in tu.diagnostics:
            print_err(f"{filepath}: " + str(d))
    elif len(tu.diagnostics) > 0 and CONFIG.VERBOSITY > 1:
        # Header entries from compdb usually generate a lot of errors
        if not filepath.endswith(".h"):
            msgs = f", {len(tu.diagnostics)-1} more message(s)" \
                    if len(tu.diagnostics) > 1 else ''
            print_err(f"{str(tu.diagnostics[0])}" + msgs)



