from dataclasses import dataclass
from typing import Set
from clang import cindex

PROJECT_DIR         = ""
DEPENDENCY_OLD      = ""

NPROC = 5

# Set the path to the clang library (platform dependent)
cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

def print_err(msg: str):
    print("\033[31m!>\033[0m " +  msg)

def get_compile_args(compile_db: cindex.CompilationDatabase,
    filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file
    and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
    compile_args                    = list(ccmds[0].arguments)

    # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
    # and add the default linker paths
    return compile_args[1:-1]

def flatten(list_of_sets: list[Set]) -> Set:
    flat = set()
    for li in list_of_sets:
        for item in li:
            flat.add(item)
    return flat


@dataclass(init=True)
class DependencyArgument:
    ''' The type is a string conversions from cindex.TypeKind '''
    type: str
    spelling: str

@dataclass(init=True)
class DependencyFunction:
    ''' 
    A function which is transativly changed due to invoking either
    a direclty changed function or another transativly changed function
    will have the `invokes_changed_function` attribute set to a non-empty list 
    '''
    filepath: str
    displayname: str # Includes the full prototype string
    name: str
    return_type: str
    arguments: list[DependencyArgument]
    line: int
    col: int

    direct_change: bool = True

    # The list contains `filepath:displayname:line:col` entries
    # we can look them up in the change_set manually if needed
    invokes_changed_functions = list[str]

    def __repr__(self):
        return f"{self.filepath}:{self.line}:{self.col}:{self.name}()"

    def __hash__(self):
        return hash(self.filepath + self.displayname + str(self.line) + str(self.col))

@dataclass(init=True)
class ProjectInvocation:
    function: DependencyFunction
    filepath: str
    line: int
    col: int

    def __repr__(self):
        return f"call to {self.function} at {self.filepath}:{self.line}:{self.col}"

@dataclass(init=True)
class SourceFile:
    new_path: str
    new_compile_args: list[str]

@dataclass(init=True)
class SourceDiff(SourceFile):
    old_path: str
    old_compile_args: list[str]

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


