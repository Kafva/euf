#!/usr/bin/env python3
'''
Approach:
1. Determine what source files in the dependency have been 
modified (M) or renamed (R) since the last commit based on git labeling 
2. Walk the AST of the old and new version of each modified file
3. Consider any functions with a difference in the AST composition as
the base change-set
4. Analyze each of the objects in the base change-set and 
remove equivilent entries
5. Walk the AST of all source files in the main project and return
all locations were functions from the change set are called
'''
import argparse, re, sys, logging, os # pylint: disable=multiple-imports
from multiprocessing import Pool
from functools import partial
from pprint import pprint
import traceback
from typing import Set
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo

from base import NPROC, DEPENDENCY_OLD, PROJECT_DIR, DependencyFunction, \
    ProjectInvocation, SourceDiff, SourceFile, flatten, get_compile_args, print_err
from preprocessing.change_set import get_changed_functions_from_diff, dump_top_level_decls
from preprocessing.impact_set import get_call_sites_from_file


# The location to store the new version of the dependency
NEW_VERSION_ROOT = "/tmp"

def compile_db_fail_msg(path: str):
    print_err(f"Failed to parse {path}/compile_commands.json\n" +
    "The compilation database can be created using `bear -- <build command>` e.g. `bear -- make`\n" +
    "Consult the documentation for the particular dependency for additional build instructions")
    done(1)

def done(code: int = 0):
    DEP_REPO.git.checkout(HEAD_BRANCH) # type: ignore
    sys.exit(code)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=
    "A 'compile_commands.json' database must be present for both the project and the dependency."
    )

    parser.add_argument("project", type=str, nargs=1,
        help='Project to analyze')
    parser.add_argument("--commit-new", metavar="hash",
        help='Git hash of the new commit in the dependency')
    parser.add_argument("--commit-old", metavar="hash",
        help='Git hash of the old (current) commit in the dependency')
    parser.add_argument("--dependency", metavar="directory", help=
        'The dependency to upgrade, should be an up-to-date git repository with the most recent commit checked out')
    parser.add_argument("--info", action='store_true', default=False,
        help='Set logging level to INFO')
    parser.add_argument("--dump-full", action='store_true', default=False,
        help='Dump the complete trace of the AST')
    parser.add_argument("--dump-top-level-decls", action='store_true', default=False,
        help='Dump the names of all top level declarations in the old version of the dependency')
    parser.add_argument("--nprocs", metavar='count', help=
        f"The number of processes to spawn for parallel execution (default {NPROC})")
    parser.add_argument("--dep-only", metavar="filepath", default="", help=
        'Only process a specific path of the dependency (uses the path in the new commit)')
    parser.add_argument("--project-only", metavar="filepath", default="", help=
        'Only process a specific path of the main project')

    args = parser.parse_args()

    #wow: Set[DependencyFunction] = set()
    #wow.add(
    #    DependencyFunction(
    #        filepath    ="wow", 
    #        displayname ="wow", 
    #        name        ="wow", 
    #        return_type ="wow", 
    #        arguments   = [ ],
    #        line = 1,
    #        col = 1
    #    ))
    #print( [ x for x in wow ] )
    #exit()

    if args.commit_new == "" or args.commit_old == "" or \
        args.dependency == "" or len(args.project) == 0:
        print("Missing required option/argument")
        sys.exit(1)

    PROJECT_DIR         = os.path.abspath(args.project[0])
    DEPENDENCY_OLD      = os.path.abspath(args.dependency)
    DEP_ONLY_PATH       = args.dep_only
    PROJECT_ONLY_PATH   = args.project_only

    # Set logging level
    LEVEL = logging.INFO if args.info else logging.ERROR
    logging.basicConfig(stream=sys.stdout, level=LEVEL,
            format="\033[34m!\033[0m: %(message)s"
    )

    # - - - Dependency - - - #
    DEP_REPO = Repo(DEPENDENCY_OLD)
    try:
        HEAD_BRANCH = DEP_REPO.active_branch
    except TypeError as e:
        print_err(f"Unable to read current branch name for {DEPENDENCY_OLD}\n{e}")
        sys.exit(1)

    # Find the objects that correspond to the old and new commit
    COMMIT_OLD: Commit = None # type: ignore
    COMMIT_NEW: Commit = None # type: ignore

    for commit in DEP_REPO.iter_commits():
        if commit.hexsha == args.commit_new:
            COMMIT_NEW: Commit = commit
        elif commit.hexsha == args.commit_old:
            COMMIT_OLD: Commit = commit

    if not COMMIT_OLD:
        print(f"Unable to find commit: {args.commit_old}")
        sys.exit(1)
    if not COMMIT_NEW:
        print(f"Unable to find commit: {args.commit_new}")
        sys.exit(1)

    # Only include modified (M) and renamed (R) '.c' files
    # Renamed files still provide us with context information when a
    # change has occurred at the same time as a move operation:
    #   e.g. `foo.c -> src/foo.c`
    COMMIT_DIFF = filter(lambda d: \
                str(d.a_path).endswith(".c") and \
                re.match("M|R", d.change_type),
                COMMIT_NEW.diff(COMMIT_OLD))
    SOURCE_DIFFS = [ SourceDiff(
                new_path = d.a_path,
                old_path = d.b_path,
                new_compile_args = [],
                old_compile_args = []
    ) for d in COMMIT_DIFF ]

    # To get the full context when parsing source files we need the
    # full source tree (and a compilation database) for both the
    # new and old version of the dependency
    DEPENDENCY_NEW = f"{NEW_VERSION_ROOT}/{os.path.basename(DEPENDENCY_OLD)}"

    if not os.path.exists(DEPENDENCY_NEW):
        logging.info(f"Creating worktree at {DEPENDENCY_NEW}")
        os.system(f"git worktree add -b euf {DEPENDENCY_NEW} {COMMIT_NEW}")

    # Ensure that the old repo has the correct commit checked out
    DEP_REPO.git.checkout(COMMIT_OLD.hexsha) # type: ignore

    # For the AST dump to contain a resolved view of the symbols
    # we need to provide the correct compile commands
    # These can be derived from compile_commands.json
    try:
        DEP_DB_NEW  = cindex.CompilationDatabase.fromDirectory(DEPENDENCY_NEW)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEPENDENCY_NEW)
    try:
        DEP_DB_OLD  = cindex.CompilationDatabase.fromDirectory(DEPENDENCY_OLD)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(DEPENDENCY_OLD)

    # Extract compile flags for each file that was changed
    for diff in SOURCE_DIFFS:
        diff.old_compile_args = get_compile_args(DEP_DB_OLD, diff.old_path)
        diff.new_compile_args = get_compile_args(DEP_DB_NEW, diff.new_path)

    if DEP_ONLY_PATH != "":
        SOURCE_DIFFS = list(filter(lambda d: d.new_path == DEP_ONLY_PATH, SOURCE_DIFFS))

    # - - - Main project - - - #
    # Gather a list of all the source files in the main project
    main_repo = Repo(PROJECT_DIR)
    SOURCE_FILES = filter(lambda p: p.endswith(".c"),
        [ e.path for e in main_repo.tree().traverse() ] # type: ignore
    )

    try:
        MAIN_DB = cindex.CompilationDatabase.fromDirectory(PROJECT_DIR)
    except cindex.CompilationDatabaseError as e:
        compile_db_fail_msg(PROJECT_DIR)

    SOURCE_FILES = [ SourceFile(
        new_path = filepath,
        new_compile_args = get_compile_args(MAIN_DB, filepath)
    ) for filepath in SOURCE_FILES ]

    if PROJECT_ONLY_PATH != "":
        SOURCE_FILES = list(filter(lambda f: f.new_path == PROJECT_ONLY_PATH, SOURCE_FILES))

    # - - - Change set - - - #
    CHANGED_FUNCTIONS: Set[DependencyFunction] = []

    # Look through the old and new version of each delta
    # using NPROC parallel processes and save
    # the changed functions to `CHANGED_FUNCTIONS`
    try:
        with Pool(NPROC) as p:
            CHANGED_FUNCTIONS       = flatten(p.map(
                partial(get_changed_functions_from_diff,
                    old_root_dir=DEPENDENCY_OLD,
                    new_root_dir=DEPENDENCY_NEW
                ),
                SOURCE_DIFFS
            ))

            print("==> Change set <==")
            if DEP_ONLY_PATH != "":
                pprint(CHANGED_FUNCTIONS)
    except Exception as e:
        logging.error(traceback.format_exc())
        done(1)


    # - - - Transitive change set propagation - - - #
    # To include functions that have not had a textual change but call a function
    # that has changed, we perform a configurable number of additional passes were we look for
    # invocations of changed functions in the dependency (and add any functions that call a changed function)
    # to the changed set.
    #

    # - - - Reduction of change set - - - #
    # Regardless of which back-end we use to check equivalance, we will need a minimal
    # program that invokes both versions of the changed function and then performs an assertion
    # on all affected outputs (only the return value for now)



    # - - - (Optional) Dump parse trees - - - #
    # Dump a list of all top level declarations in the old version
    # of each file with a diff
    if args.dump_top_level_decls or args.dump_full:
        print("==> Dump dependency (old) <===")
        os.chdir(DEPENDENCY_OLD)
        for diff in SOURCE_DIFFS:
            # Reads from in-memory content of each diff
            tu_old = cindex.TranslationUnit.from_source(
                    f"{DEPENDENCY_OLD}/{diff.old_path}",
                    args = diff.old_compile_args
            )
            cursor: cindex.Cursor = tu_old.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)

        print("==> Dump dependency (new) <===")
        os.chdir(DEPENDENCY_NEW)
        for diff in SOURCE_DIFFS:
            # Reads content from files on disk
            tu_new = cindex.TranslationUnit.from_source(
                    f"{DEPENDENCY_NEW}/{diff.new_path}",
                    args = diff.new_compile_args
            )
            cursor: cindex.Cursor = tu_new.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)

        print("==> Dump project <===")
        os.chdir(PROJECT_DIR)

        for source_file in SOURCE_FILES:
            # Reads content from files on disk
            tu = cindex.TranslationUnit.from_source(
                    f"{PROJECT_DIR}/{source_file.new_path}",
                    args = source_file.new_compile_args
            )
            cursor: cindex.Cursor = tu.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)
        done(0)


    # - - - Impact set - - - #
    CALL_SITES: list[ProjectInvocation]      = []

    os.chdir(PROJECT_DIR)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations
    try:
        with Pool(NPROC) as p:
            CALL_SITES = flatten(p.map(
                partial(get_call_sites_from_file, changed_functions=CHANGED_FUNCTIONS),
                SOURCE_FILES
            ))

            print("==> Impact set <==")
            if PROJECT_ONLY_PATH != "":
                pprint(CALL_SITES)
    except Exception as e:
        logging.error(traceback.format_exc())
        done(1)


    done(0)
