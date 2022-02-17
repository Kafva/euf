#!/usr/bin/env python3
import argparse
from enum import Enum
from logging import error
from dataclasses import dataclass
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo
from pprint import pprint

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
    CURRENT = "current"
    NEW = "new"


def get_changed_functions(cursor_curr: cindex.Cursor, cursor_new: cindex.Cursor) -> list[Function]:
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

    def extract_pairs(cursor: cindex.Cursor, cursor_pairs: dict, key: CursorContext) -> None:
        for c in cursor.get_children():
            if str(c.kind).endswith("FUNCTION_DECL") and c.is_definition():

                if c.displayname in cursor_pairs:
                    cursor_pairs[c.displayname][key] = c
                else:
                    cursor_pairs[c.displayname]      = { key: c }
    
    def functions_differ(cursor_curr: cindex.Cursor, cursor_new: cindex.Cursor) -> bool:
        ''' Type-check the arguments recursively '''
        for t1,t2 in zip( cursor_curr.get_arguments(), cursor_new.get_arguments() ):
            #print(t1.get_usr(), t2.get_usr())
            if t1.kind != t2.kind:
                return True

        for c1,c2 in zip(cursor_curr.get_children(), cursor_new.get_children()):
            if functions_differ(c1,c2):
                return True

        return False

    extract_pairs(cursor_curr, cursor_pairs, CursorContext.CURRENT)
    extract_pairs(cursor_new, cursor_pairs,  CursorContext.NEW)
    
    for key in cursor_pairs:
        # If the function pairs differ based on AST traversal, add them to the list of 
        # changed_functions. 
        # If the function prototypes differ, we can assume that an influential change has occured
        # and we do not need to perform a deeper SMT analysis

        if not CursorContext.NEW in cursor_pairs[key]:
            print(f"=> Deleted: {cursor_curr.displayname}")
            continue
        elif not CursorContext.CURRENT in cursor_pairs[key]:
            print(f"=> New: {cursor_new.displayname}")
            continue
        
        cursor_curr = cursor_pairs[key][CursorContext.CURRENT]
        cursor_new = cursor_pairs[key][CursorContext.NEW]

        if functions_differ(cursor_curr, cursor_new):

            function = Function( 
                displayname = cursor_curr.displayname,
                name = cursor_curr.spelling,
                return_type = cursor_curr.type.get_result().kind,
                arguments = [ (t.kind,n.spelling) for t,n in zip(cursor_curr.type.argument_types(), cursor_curr.get_arguments()) ]
            )

            print(f"=> Differ: {function.displayname}")
            changed_functions.append(function)
        else:
            print(f"=> Same: {cursor_curr.displayname}")


    return changed_functions
    
def dump_functions_in_tu(cursor: cindex.Cursor) -> None:
    '''
    By inspecting the AST we can determine what tokens are function declerations
    https://libclang.readthedocs.io/en/latest/index.html#clang.cindex.TranslationUnit.from_source
    '''
    if str(cursor.kind).endswith("FUNCTION_DECL") and cursor.is_definition():

        print(f"{cursor.type.get_result().spelling} {cursor.spelling} ("); # cursor.type.get_result().kind

        for t,n in zip(cursor.type.argument_types(), cursor.get_arguments()):
                print(f"\t{t.spelling} {n.spelling}") # t.kind
        print(")")

    for c in cursor.get_children():
        dump_functions_in_tu(c)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="")

    parser.add_argument("project", type=str, nargs=1,
        help='Project to analyze')
    parser.add_argument("-n", "--commit-new",
        help='Git hash of the updated commit in the dependency')
    parser.add_argument("-c", "--commit-current",
        help='Git hash of the current commit in the dependency')
    parser.add_argument("-d", "--dependency", help =
        'Path to the directory with source code for the dependency to upgrade')

    args = parser.parse_args()

    if args.commit_new == "" or args.commit_current == "" or \
        args.dependency == "" or len(args.project) == 0:
        print("Missing required option/argument")
        exit(1)

    PROJECT = args.project[0]
    DEPENDENCY_DIR = args.dependency

    # Approach:
    # 0. Determine what source files have been modified
    # 1. Walk the AST of the current and new version of each file
    # 2. Consider any functions with a difference in the AST composition as changed

    CHANGED_FUNCTIONS: dict[str,list[Function]] = {}

    dep_repo = Repo(DEPENDENCY_DIR)

    # Find the objects that correspond to the current and new commit
    for commit in dep_repo.iter_commits():
        if commit.hexsha == args.commit_new:
            COMMIT_NEW: Commit = commit
        elif commit.hexsha == args.commit_current:
            COMMIT_CURRENT: Commit = commit

    # Only include modifications (M) to '.c' files
    try:
        COMMIT_DIFF = filter(lambda d: 
                    str(d.a_path).endswith(".c") and d.change_type == "M", 
                    COMMIT_NEW.diff(COMMIT_CURRENT))
    except NameError as error:
        print(f"Unable to find commit: {error.name}")
        exit(1)

    
    for diff in COMMIT_DIFF:
        #a_diff = diff.a_blob.data_stream.read().decode('utf-8')
        #b_diff = diff.b_blob.data_stream.read().decode('utf-8')

        if diff.a_path != "src/big5.c": continue
        
        tu_curr = cindex.TranslationUnit.from_source(
                f"{DEPENDENCY_DIR}/{diff.b_path}",
                unsaved_files=[ (f"{DEPENDENCY_DIR}/{diff.b_path}", diff.b_blob.data_stream) ]
        )
        cursor_curr: cindex.Cursor = tu_curr.cursor
        #print("===> Current state <====")
        #dump_functions_in_tu(cursor_curr)

        tu_new = cindex.TranslationUnit.from_source(f"{DEPENDENCY_DIR}/{diff.a_path}")
        cursor_new: cindex.Cursor = tu_new.cursor
        #print("===> New state <====")
        #dump_functions_in_tu(cursor_new)

        if diff.a_path in CHANGED_FUNCTIONS:
            CHANGED_FUNCTIONS[diff.a_path].extend( get_changed_functions(cursor_curr, cursor_new) )
        else:
            CHANGED_FUNCTIONS[diff.a_path] = get_changed_functions(cursor_curr, cursor_new)

        pprint(CHANGED_FUNCTIONS)
        break

