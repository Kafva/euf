import sys
from dataclasses import dataclass
from clang import cindex

# Enable importing from the root directory inside the module
sys.path.append('../')

PROJECT_DIR         = ""
DEPENDENCY_OLD      = ""

NPROC = 5

# Set the path to the clang library (platform dependent)
cindex.Config.set_library_file("/usr/lib/libclang.so.13.0.1")

def get_compile_args(compile_db: cindex.CompilationDatabase,
    filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file
    and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
    compile_args                    = list(ccmds[0].arguments)

    # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
    # and add the default linker paths
    return compile_args[1:-1]

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

    We pair functions based on the key:
    {diff.new_path}:{diff.old_path}:{child.spelling}
    All other attributes could thus differ between the new and old version.

    '''
    displayname: str # Includes the full prototype string
    name: str # Same between changes but used for __repr__
    filepath: str
    return_type: str
    arguments: list[DependencyArgument]
    line: int
    col: int


    @classmethod
    def new_from_cursor(cls, filepath: str, cursor: cindex.Cursor):
        return cls(
            filepath    = filepath,
            displayname = cursor.displayname,
            name        = cursor.spelling,
            return_type = str(cursor.type.get_result().kind),
            arguments   = [ DependencyArgument( \
                    type = str(n.type.kind), \
                    spelling = str(n.spelling) \
                 ) for n in cursor.get_arguments() ],
            line = cursor.location.line,
            col = cursor.location.column
        )

    @classmethod
    def empty(cls):
        return cls(
            filepath    = "",
            displayname = "",
            name        = "",
            return_type = "",
            arguments   = [],
            line = 0,
            col = 0
        )


    def __repr__(self):
        return f"{self.filepath}:{self.line}:{self.col}:{self.name}()"

    def __hash__(self):
        return hash(self.filepath + self.return_type + self.displayname +
                str(self.line) + str(self.col))

@dataclass(init=True)
class DependencyFunctionChange:
    '''
    We pair functions based on the key:
        {diff.new_path}:{diff.old_path}:{child.spelling}
    All other attributes could thus differ between the new and old version.
    '''
    old: DependencyFunction
    new: DependencyFunction

    # The list contains `filepath:displayname:line:col` entries
    # The line and col references the new version of the dependency
    invokes_changed_functions = list[str]()
    direct_change: bool = True

    @classmethod
    def new_from_cursors(cls, old_filepath: str, new_filepath: str,
            old_cursor: cindex.Cursor, new_cursor: cindex.Cursor):
        return cls(
            old = DependencyFunction.new_from_cursor(old_filepath, old_cursor),
            new = DependencyFunction.new_from_cursor(new_filepath, new_cursor)
        )

    def __repr__(self):
        out =   "Direct change: " if self.direct_change else \
                "Indirect change: "
        out += f"{self.old} -> {self.new}"
        for trans_call in self.invokes_changed_functions:
            out += f"\n\t{trans_call}"
        return out

    def __hash__(self):
        ''' 
        Note that the hash does not consider the `invokes_changed_functions` 
        list. A set will thus only include one copy of each function
        '''
        return hash(hash(self.old) + hash(self.new))

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



