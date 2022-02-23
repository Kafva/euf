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
from git.objects.commit import Commit
from git.repo import Repo

from base import NPROC, DEPENDENCY_DIR, PROJECT_DIR, DependencyFunction, ProjectInvocation, \
    SourceDiff, SourceFile, flatten, get_compile_args, load_compile_db
from preprocessing.change_set import get_changed_functions_from_diff
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
    CHANGED_FUNCTIONS: list[DependencyFunction] = []

    # For the paths in the compilation database to be correct
    # we need to `cd` into project
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

    # - - - Reduction of change set - - - #
    # Regardless of which back-end we use to check equivalance, we will need a minimal
    # program that invokes both versions of the changed function and then performs an assertion
    # on all affected outputs (only the return value for now)
    #
    # We need:
    #   - The C-code for both versions of the changed function, in a format were both can be simultaneously resolved
    #   - The old and new version will haft to reside in different files 
    #       (e.g. what if a changed function calls a new function that did not exist earlier?)
    #   Rename all globals in the old file with *_old and all globals in the new file with *_new ?
    #   That could almost be enough... It will not be enough if other #include directives circularly
    #   import symbols from the file.
    #   For import resolutions to work as intended we essentially need two mirrors of the repo, import paths etc. could differ
    #   Switching git branches won't really work since our entrypoint needs access to both....
    #   Maybe we can compile both files through basic inlining (just expand #includes)? Then they become portable?
    #    
    #   - A new entrypoint that can call both of them
    #   - Correct imports in the entrypoint to access all type specifiers etc.

    # ... Later ...
    # - How do we determine which parameters should be completely unknown and which should be assumed etc.?



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
