from dataclasses import dataclass
from typing import TextIO
from clang import cindex


PROJECT_DIR         = ""
DEPENDENCY_DIR      = ""

NPROC = 5

# Set the path to the clang library (platform dependent)
cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

# Clang objects cannot be passed as single arguments through `partial` in
# the same way as a `str` or other less complicated objects when using mp.Pool
# We therefore need to rely on globals for the index and compilation databases
global IDX

CLANG_INDEX = cindex.Index.create()

def load_compile_db(path: str) -> cindex.CompilationDatabase:
    '''
    For the AST dump to contain a resolved view of the symbols
    we need to provide the correct compile commands
    These can be derived from compile_commands.json
    '''
    try:
        db = cindex.CompilationDatabase.fromDirectory(path)
    except cindex.CompilationDatabaseError:
        print(f"Failed to parse {path}/compile_commands.json")
        exit(1)
    return db

def get_compile_args(db: cindex.CompilationDatabase, filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = db.getCompileCommands(filepath)
    compile_args                    = [ arg for arg in ccmds[0].arguments ]

    # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
    return compile_args[1:-1]


@dataclass(init=True)
class Function:
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

    def __repr__(self):
        return f"{self.filepath}:{self.name}()"

@dataclass(init=True)
class Invocation:
    function: Function
    filepath: str
    line: int
    col: int

    def __repr__(self):
        return f"Call to {self.function} at {self.filepath}:{self.line}:{self.col}"

@dataclass(init=True)
class CursorPair:
    new: cindex.Cursor | None
    old: cindex.Cursor | None

    def __init__(self):
        self.new = None
        self.old = None

    def add(self, cursor: cindex.Cursor, is_new: bool):
        if is_new:
            self.new = cursor
        else:
            self.old = cursor

@dataclass(init=True)
class SourceFile:
    new_path: str
    compile_args: list[str]

@dataclass(init=True)
class SourceDiff(SourceFile):
    old_path: str
    old_content: bytes


def flatten(list_of_list: list[list]) -> list:
    flat = []
    for li in list_of_list:
        flat.extend(li)
    return flat


