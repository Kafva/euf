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
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo

from base import NPROC, DEPENDENCY_DIR, PROJECT_DIR, DependencyFunction, ProjectInvocation, \
    SourceDiff, SourceFile, flatten, get_compile_args, load_compile_db
from preprocessing.change_set import get_changed_functions_from_diff, dump_top_level_decls
from preprocessing.impact_set import get_call_sites_from_file

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
        'The dependency to upgrade')
    parser.add_argument("--info", action='store_true', default=False,
        help='Set logging level to INFO')
    parser.add_argument("--dump-full", action='store_true', default=False,
        help='Dump the complete trace of the AST')
    parser.add_argument("--dump-top-level-decls", action='store_true', default=False,
        help='Dump the names of all top level declerations in the old version of the dependency')
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
        sys.exit(1)

    PROJECT_DIR         = args.project[0]
    DEPENDENCY_DIR      = args.dependency
    DEP_ONLY_PATH       = args.dep_only
    PROJECT_ONLY_PATH   = args.project_only

    # Set logging level
    LEVEL = logging.INFO if args.info else logging.ERROR
    logging.basicConfig(stream=sys.stdout, level=LEVEL,
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
        sys.exit(1)

    DEP_DB  = load_compile_db(DEPENDENCY_DIR)

    # Extract compile flags for each file that was changed
    # TODO: The flags could differ between the commits
    for diff in SOURCE_DIFFS:
        diff.compile_args = get_compile_args(DEP_DB, diff.new_path)

    if DEP_ONLY_PATH != "":
        SOURCE_DIFFS = list(filter(lambda d: d.new_path == DEP_ONLY_PATH, SOURCE_DIFFS))

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
        SOURCE_FILES = list(filter(lambda f: f.new_path == PROJECT_ONLY_PATH, SOURCE_FILES))


    # - - - Change set - - - #
    CHANGED_FUNCTIONS: list[DependencyFunction] = []

    # For the paths in the compilation database to be correct
    # we need to `cd` into the project
    # TODO: The "directory" parameter in the compile_commands actually
    # gives this information for every TU
    os.chdir(DEPENDENCY_DIR)

    # Look through the old and new version of each delta
    # using NPROC parallel processes and save
    # the changed functions to `CHANGED_FUNCTIONS`
    with Pool(NPROC) as p:
        CHANGED_FUNCTIONS       = flatten(p.map(
            partial(get_changed_functions_from_diff, root_dir=DEPENDENCY_DIR),
            SOURCE_DIFFS
        ))

        print("==> Change set <==")
        if DEP_ONLY_PATH != "":
            pprint(CHANGED_FUNCTIONS)


    # - - - Transative change set propogation - - - #
    # To include functions that have not had a textual change but call a function
    # that has changed, we perform a configurable number of additional passes were we look for
    # invocations of changed functions in the dependency

    # - - - Reduction of change set - - - #
    # Regardless of which back-end we use to check equivalance, we will need a minimal
    # program that invokes both versions of the changed function and then performs an assertion
    # on all affected outputs (only the return value for now)



    # - - - Dump parse tree - - - #
    # Dump a list of all top level declerations in the old version
    # of each file with a diff (TODO multiprocessing)
    if args.dump_top_level_decls or args.dump_full:
        print("==> Dump dependency (old) <===")
        os.chdir(DEPENDENCY_DIR)
        for diff in SOURCE_DIFFS:
            # Reads from in-memory content of each diff
            tu_old = cindex.TranslationUnit.from_source(
                    f"{DEPENDENCY_DIR}/{diff.old_path}",
                    unsaved_files=[ (f"{DEPENDENCY_DIR}/{diff.old_path}", diff.old_content) ],
                    args = diff.compile_args
            )
            cursor: cindex.Cursor = tu_old.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)

        print("==> Dump dependency (new) <===")
        for diff in SOURCE_DIFFS:
            # Reads content from files on disk
            tu_new = cindex.TranslationUnit.from_source(
                    f"{DEPENDENCY_DIR}/{diff.new_path}",
                    args = diff.compile_args
            )
            cursor: cindex.Cursor = tu_new.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)

        print("==> Dump project <===")
        os.chdir(PROJECT_DIR)

        for source_file in SOURCE_FILES:
            # Reads content from files on disk
            tu = cindex.TranslationUnit.from_source(
                    f"{PROJECT_DIR}/{source_file.new_path}",
                    args = source_file.compile_args
            )
            cursor: cindex.Cursor = tu.cursor
            dump_top_level_decls(cursor, recurse = args.dump_full)
        sys.exit(0)


    # - - - Impact set - - - #
    CALL_SITES: list[ProjectInvocation]      = []

    os.chdir(PROJECT_DIR)

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations
    with Pool(NPROC) as p:
        CALL_SITES = flatten(p.map(
            partial(get_call_sites_from_file, changed_functions=CHANGED_FUNCTIONS),
            SOURCE_FILES
        ))

        print("==> Impact set <==")
        if PROJECT_ONLY_PATH != "":
            pprint(CALL_SITES)
