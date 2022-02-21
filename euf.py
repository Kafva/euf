#!/usr/bin/env python3
import argparse
from logging import error
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo
from pprint import pprint
from multiprocessing import Pool

from base import NPROC, Function
from preprocessing.change_set import get_changed_functions
from preprocessing.impact_set import find_call_sites_in_tu

CHANGED_FUNCTIONS: dict[str,list[Function]] = {}
CHANGED_FUNCTION_NAMES = []
CALL_SITES: dict[str,list[str]] = {} # 'path': [ linenr/functionname ]

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

# + Relying on the LLVM diff directly would eliminate the need for parsing out 
# comments and would give us a direct mapping as to where we want to point 
# llvm2smt. It also auto-expands macros from what I understand.

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
        #p.map(partial(process_delta, diff=COMMIT_DIFF), CHANGED_FUNCTIONS)
        p.map(process_delta, COMMIT_DIFF)

    # TODO reduce result to global location
    pprint(CHANGED_FUNCTIONS)

    # ... TODO SMT reduction of change set ... #

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations
    main_repo = Repo(PROJECT)

    SOURCE_FILES = filter(lambda p: p.endswith(".c"),
        [ e.path for e in main_repo.commit().tree.traverse() ]
    )


    for filename in CHANGED_FUNCTIONS:
        CHANGED_FUNCTION_NAMES.extend( list(map(lambda f:
            f.name, CHANGED_FUNCTIONS[filename]
        )))

    for filepath in SOURCE_FILES:
        if filepath != "src/lexer.c": continue

        tu: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(f"{PROJECT}/{filepath}")
        cursor: cindex.Cursor       = tu.cursor

        find_call_sites_in_tu(filepath, cursor, CHANGED_FUNCTION_NAMES, CALL_SITES)

    pprint(CALL_SITES)
