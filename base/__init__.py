import sys
from dataclasses import dataclass
from clang import cindex

PROJECT_DIR         = ""
DEPENDENCY_DIR      = ""

NPROC = 5

# Set the path to the clang library (platform dependent)
cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

# Clang objects cannot be passed as single arguments through `partial` in
# the same way as a `str` or other less complicated objects when using mp.Pool
# We therefore need to rely on globals for the index and compilation databases

def load_compile_db(path: str) -> cindex.CompilationDatabase:
    '''
    For the AST dump to contain a resolved view of the symbols
    we need to provide the correct compile commands
    These can be derived from compile_commands.json
    '''
    try:
        compile_db = cindex.CompilationDatabase.fromDirectory(path)
    except cindex.CompilationDatabaseError:
        print(f"Failed to parse {path}/compile_commands.json")
        sys.exit(1)
    return compile_db

def get_compile_args(compile_db: cindex.CompilationDatabase,
    filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file
    and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
    compile_args                    = list(ccmds[0].arguments)

    # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
    return compile_args[1:-1]

def flatten(list_of_lists: list[list]) -> list:
    flat = []
    for item in list_of_lists:
        flat.extend(item)
    return flat

@dataclass(init=True)
class DependencyFunction:
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[tuple[cindex.TypeKind,str]]

    def __repr__(self):
        return f"{self.filepath}:{self.name}()"

@dataclass(init=True)
class ProjectInvocation:
    function: DependencyFunction
    filepath: str
    line: int
    col: int

    def __repr__(self):
        return f"Call to {self.function} at {self.filepath}:{self.line}:{self.col}"

@dataclass(init=True)
class SourceFile:
    new_path: str
    compile_args: list[str]

@dataclass(init=True)
class SourceDiff(SourceFile):
    old_path: str
    old_content: bytes

@dataclass(init=True)
class CursorPair:
    new: cindex.Cursor
    old: cindex.Cursor
    new_path: str
    old_path: str

    def __init__(self):
        self.new = None # type: ignore
        self.old = None # type: ignore

    def add(self, cursor: cindex.Cursor, diff:SourceDiff, is_new: bool):
        ''' Add the provided cursor and its filepath to the pair '''
        if is_new:
            self.new = cursor
            self.new_path = diff.new_path
        else:
            self.old = cursor
            self.old_path = diff.old_path


