#!/usr/bin/env python3
import argparse, re, sys, logging, os
from logging import error
from clang import cindex
from git.objects.commit import Commit
from git.repo import Repo
from git import Diff
from multiprocessing import Pool
from base import NPROC, Function, Invocation, flatten
from pprint import pprint
from preprocessing.change_set import get_changed_functions_in_path
from preprocessing.impact_set import find_call_sites_in_tu

# Relying on the LLVM diff directly would eliminate the need for parsing out 
# comments and would give us a direct mapping as to where we want to point 
# llvm2smt. It also auto-expands macros from what I understand.

CHANGED_FUNCTIONS: list[Function] = []
CHANGED_FUNCTION_NAMES: list[str] = []
CALL_SITES: list[Invocation]      = []

# Create an index for clang
IDX = cindex.Index.create()

# TODO Globals -> ProcessManager ?
def get_changed_functions_from_diff(diff: Diff) -> list[Function]:
    '''
    The from_source() method accepts content from arbitrary text streams,
     allowing us to analyze the old version of each file
    '''
    tu_old = cindex.TranslationUnit.from_source(
            f"{DEPENDENCY_DIR}/{diff.b_path}",
            unsaved_files=[ (f"{DEPENDENCY_DIR}/{diff.b_path}", diff.b_blob.data_stream) ],
            index=IDX
    )
    cursor_old: cindex.Cursor = tu_old.cursor

    tu_new = cindex.TranslationUnit.from_source(f"{DEPENDENCY_DIR}/{diff.a_path}", index=IDX)
    cursor_new: cindex.Cursor = tu_new.cursor

    return get_changed_functions_in_path(cursor_old, cursor_new, new_path=diff.a_path)

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
    f'Number of processes to spawn for parallel execution (default {NPROC})')
parser.add_argument("--dep-only", metavar="filepath", default="", help=
    'Only process a specififc path of the dependency (uses the path in the new commit)')
parser.add_argument("--project-only", metavar="filepath", default="", help=
    'Only process a specififc path of the main project')

args = parser.parse_args()

if args.commit_new == "" or args.commit_old == "" or \
    args.dependency == "" or len(args.project) == 0:
    print("Missing required option/argument")
    exit(1)

PROJECT             = args.project[0]
DEPENDENCY_DIR      = args.dependency
DEP_ONLY_PATH       = args.dep_only
PROJECT_ONLY_PATH   = args.project_only

# Set logging level
level = logging.INFO if args.info else logging.ERROR
logging.basicConfig(stream=sys.stdout, level=logging.DEBUG,
        format="\033[34m!\033[0m: %(message)s"
)

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

# Only include modified (M) and renamed (R) '.c' files
# Renamed files still provide us with context information when a
# change has occured at the same time as a move operation: 
#   e.g. `foo.c -> src/foo.c`
try:
    COMMIT_DIFF = filter(lambda d: \
                str(d.a_path).endswith(".c") and re.match("M|R", d.change_type),
                COMMIT_NEW.diff(COMMIT_CURRENT))
    if DEP_ONLY_PATH != "":
        COMMIT_DIFF = filter(lambda d: d.a_path == DEP_ONLY_PATH, COMMIT_DIFF)
except NameError as error:
    print(f"Unable to find commit: {error.name}")
    exit(1)

# Gather a list of all the source files in the main project
main_repo = Repo(PROJECT)
SOURCE_FILES = filter(lambda p: p.endswith(".c"),
    [ e.path for e in main_repo.commit().tree.traverse() ]
)


# Look through the old and new version of each delta
# using NPROC parallel processes and save the
# the changed functions to `CHANGED_FUNCTIONS`
with Pool(NPROC) as p:
    # Each diff in COMMIT_DIFF is given its own invocation of `get_changed_functions_from_diff`
    CHANGED_FUNCTIONS       = flatten(p.map(get_changed_functions_from_diff, COMMIT_DIFF))
    CHANGED_FUNCTION_NAMES  = list(map(lambda f: f.name, CHANGED_FUNCTIONS))

    print("==> Change set <==")
    if DEP_ONLY_PATH != "": pprint(CHANGED_FUNCTIONS)

    # ... TODO SMT reduction of change set ... #

    # With the changed functions enumerated we can
    # begin parsing the source code of the main project
    # to find all call locations

    # For the AST dump to contain a resolved view of the symbols
    # we need to provide all of the correct compile commands
    # These can be dervied from compile_commands.json
    try:
        db = cindex.CompilationDatabase.fromDirectory(PROJECT)
        os.chdir(PROJECT)
    except cindex.CompilationDatabaseError as error:
        print(error)
        exit(1)

    for filepath in SOURCE_FILES:
        if PROJECT_ONLY_PATH != "" and filepath != PROJECT_ONLY_PATH: continue

        # Load the compilation configuration for the perticular file
        ccmds: cindex.CompileCommands   = db.getCompileCommands(filepath)
        compile_args                    = [ arg for arg in ccmds[0].arguments ]

        # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
        compile_args = compile_args[1:-1]

        tu: cindex.TranslationUnit  = cindex.TranslationUnit.from_source(filepath, args = compile_args, index=IDX)
        cursor: cindex.Cursor       = tu.cursor

        find_call_sites_in_tu(filepath, cursor, CHANGED_FUNCTION_NAMES, CALL_SITES)

    print("==> Impact set <==")
    if PROJECT_ONLY_PATH != "": pprint(CALL_SITES)
