#!/usr/bin/env python3
import argparse, re, sys, logging, os
from git.objects.commit import Commit
from git.objects.tree import Tree
from git.repo import Repo
from multiprocessing import Pool
from functools import partial
from pprint import pprint

from base import NPROC, Function, Invocation, SourceDiff, SourceFile, flatten, DEPENDENCY_DIR, PROJECT_DIR, get_compile_args, load_compile_db
from preprocessing.change_set import get_changed_functions_from_diff
from preprocessing.impact_set import get_call_sites_from_file

# Relying on the LLVM diff directly would eliminate the need for parsing out 
# comments and would give us a direct mapping as to where we want to point 
# llvm2smt. It also auto-expands macros from what I understand.

CHANGED_FUNCTIONS: list[Function] = []
CALL_SITES: list[Invocation]      = []

# Approach:
# 0. Determine what source files have been modified
# 1. Walk the AST of the old and new version of each file
# 2. Consider any functions with a difference in the AST composition as changed
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="")

    parser.add_argument("project", type=str, nargs=1,
        help='Project to analyze')
    parser.add_argument("--commit-new", metavar="hash",
        help='Git hash of the updated commit in the dependency')
    parser.add_argument("--commit-old", metavar="hash",
        help='Git hash of the old commit in the dependency')
    parser.add_argument("--dependency", metavar="directory", help=
        'Path to the directory with source code for the dependency to upgrade')
    parser.add_argument("--info", action='store_true', default=False,
        help='Set INFO level for logging')
    parser.add_argument("--nprocs", metavar='count', help=
        f"The number of processes to spawn for parallel execution (default {NPROC})")
    parser.add_argument("--dep-only", metavar="filepath", default="", help=
        'Only process a specific path of the dependency (uses the path in the new commit)')
    parser.add_argument("--project-only", metavar="filepath", default="", help=
        'Only process a specific path of the main project')

    args = parser.parse_args()

    if args.commit_new == "" or args.commit_old == "" or \
        args.dependency == "" or len(args.project) == 0:
        print("Missing required option/argument")
        exit(1)

    PROJECT_DIR         = args.project[0]
    DEPENDENCY_DIR      = args.dependency
    DEP_ONLY_PATH       = args.dep_only
    PROJECT_ONLY_PATH   = args.project_only

    # Set logging level
    level = logging.INFO if args.info else logging.ERROR
    logging.basicConfig(stream=sys.stdout, level=logging.DEBUG,
            format="\033[34m!\033[0m: %(message)s"
    )

    # - - - Dependency - - - #
    dep_repo = Repo(DEPENDENCY_DIR)

    # Find the objects that correspond to the old and new commit
    for commit in dep_repo.iter_commits():
        if commit.hexsha == args.commit_new:
            COMMIT_NEW: Commit = commit
        elif commit.hexsha == args.commit_old:
            COMMIT_CURRENT: Commit = commit

    # Only include modified (M) and renamed (R) '.c' files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation: 
    #   e.g. `foo.c -> src/foo.c`
    try:
        COMMIT_DIFF = filter(lambda d: \
                    str(d.a_path).endswith(".c") and re.match("M|R", d.change_type),
                    COMMIT_NEW.diff(COMMIT_CURRENT))
        SOURCE_DIFFS = [ SourceDiff(
                    new_path = d.a_path,
                    old_path = d.b_path,
                    old_content = d.b_blob.data_stream.read(),
                    compile_args = []
                ) for d in COMMIT_DIFF ]
    except NameError as error:
        print(f"Unable to find commit: {error.name}")
        exit(1)

    DEP_DB  = load_compile_db(DEPENDENCY_DIR)

    # Extract compile flags for each file that was changed
    # TODO: The flags could differ between the commits
    for diff in SOURCE_DIFFS:
        diff.compile_args = get_compile_args(DEP_DB, diff.new_path)

    if DEP_ONLY_PATH != "":
        SOURCE_DIFFS = filter(lambda d: d.new_path == DEP_ONLY_PATH, SOURCE_DIFFS)

    # - - - Main project - - - #
    # Gather a list of all the source files in the main project
    main_repo = Repo(PROJECT_DIR)
    SOURCE_FILES = filter(lambda p: p.endswith(".c"),
        [ e.path for e in main_repo.tree().traverse() ] # type: ignore
    )

    MAIN_DB = load_compile_db(PROJECT_DIR)

    SOURCE_FILES = [ SourceFile(
        new_path = filepath,
        compile_args = get_compile_args(MAIN_DB, filepath)
    ) for filepath in SOURCE_FILES ]

    if PROJECT_ONLY_PATH != "":
        SOURCE_FILES = filter(lambda f: f.new_path == PROJECT_ONLY_PATH, SOURCE_FILES)


    # - - - Change set - - - #
    # Read in the compile_databases once
    # Sequentially parse out the compile_args for each file
    # and provide them as a list of arguments to the p.map
    # Using a global database that each worker() reads from
    # causes conccurency issues


    # Look through the old and new version of each delta
    # using NPROC parallel processes and save
    # the changed functions to `CHANGED_FUNCTIONS`
    with Pool(NPROC) as p:
        # For the paths in the compilation database to be correct
        # we need to `cd` into project
        os.chdir(DEPENDENCY_DIR)

        # Each diff in SOURCE_DIFFS is given its own invocation of `get_changed_functions_from_diff`
        CHANGED_FUNCTIONS       = flatten(p.map(
            partial(get_changed_functions_from_diff, root_dir=DEPENDENCY_DIR),
            SOURCE_DIFFS
        ))

        print("==> Change set <==")
        if DEP_ONLY_PATH != "": pprint(CHANGED_FUNCTIONS)

        # - - - TODO SMT reduction of change set - - - #

        # With the changed functions enumerated we can
        # begin parsing the source code of the main project
        # to find all call locations
        #os.chdir(PROJECT_DIR)

        #CALL_SITES = flatten(p.map(
        #    partial(get_call_sites_from_file, changed_functions=CHANGED_FUNCTIONS),
        #    SOURCE_FILES
        #))

        #print("==> Impact set <==")
        #if PROJECT_ONLY_PATH != "": pprint(CALL_SITES)

    os.chdir(PROJECT_DIR)
    for source_file in SOURCE_FILES:

        CALL_SITES.extend( get_call_sites_from_file(source_file, changed_functions=CHANGED_FUNCTIONS) )
        ## Load the compilation configuration for the particular file
        #ccmds: cindex.CompileCommands   = MAIN_DB.getCompileCommands(filepath)
        #compile_args                    = [ arg for arg in ccmds[0].arguments ]

        ## Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
        #compile_args = compile_args[1:-1]

        #tu: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(filepath, args = compile_args, index=CLANG_INDEX)
        #cursor: cindex.Cursor       = tu.cursor

        #find_call_sites_in_tu(filepath, cursor, CHANGED_FUNCTIONS, CALL_SITES)

    print("==> Impact set <==")
    if PROJECT_ONLY_PATH != "": pprint(CALL_SITES)

