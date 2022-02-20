#!/usr/bin/env python3
import argparse
from enum import Enum
from logging import error
from dataclasses import dataclass
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo
from pprint import pprint
from itertools import zip_longest
from multiprocessing import Pool

DEBUG = False
NPROC = 5


# Next steps:
#   1. Cross referencing with the main project
#       - Grep for the identified function names
#       - Parse the AST of files (in parallel) that match and display the relevant call-traces
#   2. SMT analysis to reduce impact set


# + Relying on the LLVM diff directly would eliminate the need for parsing out comments and would
# give us a direct mapping as to where we want to point llvm2smt
# - This would involve compiling the dependency in a custom manner where the 
# IR of every TU is dumped
#   before and after the change
# and then diffing these files. It also becomes more difficult to connect 
# the changes in the dependency to points in the project

# How are macros translated to LLVM?
# If a change occurs in macro (function) we would like to analyze this as well

# TODO: (not an immediate priority)
#   1. Exclusion of functions were the change only concerns a comment
#   2. Exclusion of functions were the change actually occurs after the 
# function @@context. The SMT detection should exclude these changes anyway but
# we don't want to perform unnecessary work

# Changes outside of function body will produce FPs where the
# body of the function before a change is still printed.
# To exclude these changes we will ensure that every -/+ is contained
# inside the {...} of the function at start of each @@ context

cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

@dataclass
class Function:
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

class CursorContext(Enum):
    CURRENT = "old"
    NEW = "new"

def debug_print(fmt: str, hl:bool = False) -> None:
    if DEBUG:
        if hl: print("\033[34m=>\033[0m ", end='')
        print(fmt)

def get_changed_functions(cursor_old: cindex.Cursor, cursor_new: cindex.Cursor, dump: bool = False) -> list[Function]:
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
        # If the function pairs differ based on AST traversal, add them to the list of 
        # changed_functions. 
        # If the function prototypes differ, we can assume that an influential change has occurred
        # and we do not need to perform a deeper SMT analysis

        if not CursorContext.NEW in cursor_pairs[key]:
            dump_print(f"Deleted: {key}")
            continue
        elif not CursorContext.CURRENT in cursor_pairs[key]:
            dump_print(f"New: {key}")
            continue

        cursor_old = cursor_pairs[key][CursorContext.CURRENT]
        cursor_new = cursor_pairs[key][CursorContext.NEW]

        function = Function(
            displayname = cursor_old.displayname,
            name = cursor_old.spelling,
            return_type = cursor_old.type.get_result().kind,
            arguments = [ (t.kind,n.spelling) for t,n in zip(cursor_old.type.argument_types(), cursor_old.get_arguments()) ]
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

def process_delta(diff):
    if diff.a_path != "src/euc_jp.c": return

    # The from_source() method accepts content from arbitrary text streams,
    # allowing us to analyze the old version of each file
    tu_curr = cindex.TranslationUnit.from_source(
            f"{DEPENDENCY_DIR}/{diff.b_path}",
            unsaved_files=[ (f"{DEPENDENCY_DIR}/{diff.b_path}", diff.b_blob.data_stream) ]
    )
    cursor_old: cindex.Cursor = tu_curr.cursor

    tu_new = cindex.TranslationUnit.from_source(f"{DEPENDENCY_DIR}/{diff.a_path}")
    cursor_new: cindex.Cursor = tu_new.cursor

    changed_list = get_changed_functions(cursor_old, cursor_new, True)

    if diff.a_path in CHANGED_FUNCTIONS:
        CHANGED_FUNCTIONS[diff.a_path].extend(changed_list)
    else:
        CHANGED_FUNCTIONS[diff.a_path] = changed_list

    pprint(CHANGED_FUNCTIONS)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="")

    parser.add_argument("project", type=str, nargs=1,
        help='Project to analyze')
    parser.add_argument("--commit-new",
        help='Git hash of the updated commit in the dependency')
    parser.add_argument("--commit-old",
        help='Git hash of the old commit in the dependency')
    parser.add_argument("--dependency", help=
        'Path to the directory with source code for the dependency to upgrade')
    parser.add_argument("--debug", action='store_true', default=False,
        help='Toggle debug output')
    parser.add_argument("--nprocs", help=
        f'Number of processes to spawn for parallel execution (default {NPROC})')

    args = parser.parse_args()

    if args.commit_new == "" or args.commit_old == "" or \
        args.dependency == "" or len(args.project) == 0:
        print("Missing required option/argument")
        exit(1)

    DEBUG   = args.debug
    PROJECT = args.project[0]
    DEPENDENCY_DIR = args.dependency

    # Approach:
    # 0. Determine what source files have been modified
    # 1. Walk the AST of the old and new version of each file
    # 2. Consider any functions with a difference in the AST composition as changed

    CHANGED_FUNCTIONS: dict[str,list[Function]] = {}

    dep_repo = Repo(DEPENDENCY_DIR)

    # Find the objects that correspond to the old and new commit
    for commit in dep_repo.iter_commits():
        if commit.hexsha == args.commit_new:
            COMMIT_NEW: Commit = commit
        elif commit.hexsha == args.commit_old:
            COMMIT_CURRENT: Commit = commit

    # Only include modifications (M) to '.c' files
    try:
        COMMIT_DIFF = filter(lambda d:
                    str(d.a_path).endswith(".c") and d.change_type == "M",
                    COMMIT_NEW.diff(COMMIT_CURRENT))
    except NameError as error:
        print(f"Unable to find commit: {error.name}")
        exit(1)


    # Look through the old and new version of each delta
    # using NPROC parallel processes and save the
    # the changed functions to `CHANGED_FUNCTIONS`
    with Pool(NPROC) as p:
        p.map(process_delta, COMMIT_DIFF)


    debug_print("Done", hl=True)


