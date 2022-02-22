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
# Unless....
# We let the master peform all .from_source() operations
# and only run the AST parsing in parallel
global IDX, DEP_DB, MAIN_DB

IDX = cindex.Index.create()
DEP_DB = None
MAIN_DB = None


def load_compile_db(path) -> cindex.CompilationDatabase:
    try:
        db = cindex.CompilationDatabase.fromDirectory(path)
    except cindex.CompilationDatabaseError:
        print(f"Failed to parse {path}/compile_commands.json")
        exit(1)
    return db



@dataclass(init=True)
class Function:
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: cindex.TypeKind
    arguments: list[ tuple[cindex.TypeKind,str] ]

    def __repr__(self):
        return f"{self.filepath}:{self.name}"

@dataclass(init=True)
class Invocation:
    function: Function
    filepath: str
    #trace: str # Call-trace in the main project to reach the invocation
    location: cindex.SourceLocation

    def __repr__(self):
        return f"{self.filepath}"

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

def flatten(list_of_list: list[list]) -> list:
    flat = []
    for li in list_of_list:
        flat.extend(li)
    return flat


