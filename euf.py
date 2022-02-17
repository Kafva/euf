#!/usr/bin/env python3
import argparse, os
from logging import error
from dataclasses import dataclass
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo

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
# we don't want to perform uneccessary work

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
    arguments: list[str]



def get_changed_functions(c1: cindex.Cursor, c2: cindex.Cursor) -> None:
    '''
    As a starting point we can walk the AST of the new and old file in parallel and
    consider any divergence (within a function) as a potential change
    '''
    pass


def dump_functions_in_tu(cursor: cindex.Cursor) -> None:
    '''
     Determining what is a function prototype through a Regex is not trivial:
      https://cs.wmich.edu/~gupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm
     By inspecting the AST we can determine what tokens are function declerations
       clang -fsyntax-only -Xclang -ast-dump ~/Repos/oniguruma/sample/bug_fix.c
     Native Python method:
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
        print("Missing required option")
        exit(1)

    PROJECT = args.project[0]
    DEPENDENCY_DIR = args.dependency

    # Approach:
    # 0. Determine what source files have been modified
    # 1. Walk the AST of the current and new version of each file
    # 2. Consider any functions with a difference in the AST composition as changed

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
        
        print("===> Current state <====")
        tu_curr = cindex.TranslationUnit.from_source(
                f"{DEPENDENCY_DIR}/{diff.b_path}",
                unsaved_files=[ (f"{DEPENDENCY_DIR}/{diff.b_path}", diff.b_blob.data_stream) ]
        )
        cursor_curr: cindex.Cursor = tu_curr.cursor
        dump_functions_in_tu(cursor_curr)

        print("===> New state <====")
        tu_new = cindex.TranslationUnit.from_source(f"{DEPENDENCY_DIR}/{diff.a_path}")
        cursor_new: cindex.Cursor = tu_new.cursor
        dump_functions_in_tu(cursor_new)


        break





























    #import re
    #import subprocess
    #EUF_ROOT = os.path.dirname(os.path.realpath(__file__))
    #DIFF_FILE = "/tmp/" + args.commit_new + ".diff"

	## Create a diff between the current and new commit at /tmp/<NEW_COMMIT>.diff
    #subprocess.run(["./scripts/euf.sh", "-c", args.commit_current, 
    #    "-n", args.commit_new, "-d", args.dependency, PROJECT], check=True
    #)

    ## There is no guarantee that a change context will start with a function
    ## name but the `--function-context` option will at least guarantee that the
    ## function enclosing every change is part of the diff
    ## As a starting point, we consider all function names in the diff changed
    #CURRENT_FILEPATH = ""
    #FILE_CONTEXT_CONTENT = ""

    #with open(DIFF_FILE, encoding='utf-8') as f:
    #    try:
    #        for line in f:
    #            context_match = re.search(
    #                r'^\s*diff --git a/([-/_0-9a-z]+\.[ch]).*', line
    #            )

    #            if context_match: # New file (TU) context
    #                
    #                # Skip the next three lines of context information
    #                # pylint: disable=W0106
    #                [ f.readline() for _ in range(3) ]

    #                # If there is content from the previous context, parse it
    #                if FILE_CONTEXT_CONTENT != "":
    #                    break;


    #                # Clear the content and update the filepath
    #                CURRENT_FILEPATH = DEPENDENCY_DIR + "/" + context_match.group(1)
    #                FILE_CONTEXT_CONTENT = ""
    #            else:
    #                FILE_CONTEXT_CONTENT += line
    #    except UnicodeDecodeError as error:
    #        print(f"Error reading {DIFF_FILE}: {error}")
