import sys, os
from pathlib import Path
from dataclasses import dataclass
from clang import cindex

from cparser.util import compact_path, get_path_relative_to, remove_prefix

# Enable importing from the root directory inside the module
sys.path.append('../')

@dataclass(init=True)
class MacroNameGenerator:
    '''
    Expat has macros which expand to several function calls using a
    custom prefix passed as an argument
    
      #define STANDARD_VTABLE(E)
      E##byteType, E##isNameMin, E##isNmstrtMin, E##byteToAscii, E##charMatches,
    
    We explicitly replace these using exact regex matching

    Note that the filepath does NOT use the --dep-source-root argument,
    the path should be relative to the .git root
    '''
    filepath: str                   # #define location (from project root)
    arg: str                 # 'E' in the example
    global_name_suffixes: list[str] # 'byteType', 'isNameMin' ...

class Config:
    VERBOSITY: int = 0
    TRANSATIVE_PASSES: int = 1
    NPROC: int = 5
    UNWIND: int = 1

    LIBCLANG = "/usr/lib/libclang.so.13.0.1"

    # A file will be considered renamed if git blame only finds
    # two origins for changes and the changes are within the ratio
    # [0.5,RENAME_RATIO_LOW]
    RENAME_RATIO_LOW: float = .3

    RENAME_BLACKLIST: str = ""
    GOTO_BUILD_SCRIPT: str = ""
    PLUGIN: str = ""

    # The location to store the new version of the dependency
    EUF_CACHE: str = f"{os.path.expanduser('~')}/.cache/euf"
    CACHE_INTERNAL_STASH: str = "INTERNAL EUF STASH"
    OUTDIR: str = ".out"
    RUN_CBMC: bool = False
    SUFFIX: str = "_old_b026324c6904b2a"

    # Toggles echoing of scripts
    SETX: str = "false"

    INIT_VIM: str = ""
    RENAME_LUA: str = ""

    # Reuse /tmp/rename.txt if present
    REUSE_EXISTING_NAMES: bool = False
    RENAME_TXT = "/tmp/rename.txt"
    RENAME_CSV: str = "/tmp/rename.csv"
    NVIM: str = "/usr/bin/nvim"
    EUF_NVIM_SOCKET: str = "/tmp/eufnvim"


    # - - - Expat - - -
    # Prefixes on the form 'PREFIX(basename)' that should trigger an 
    # exact string replacement rather than a ccls replacement
    PREFIXES = [ "little2_", "normal_", "big2_" ] # followed by 'basename'
    PREFIX_MACRO = "PREFIX"

    NAME_GENERATORS: list[MacroNameGenerator]



global CONFIG
CONFIG = Config()

C_SYMBOL_CHARS = "[_0-9a-zA-Z]"

if not os.path.exists(CONFIG.EUF_CACHE):
    os.mkdir(CONFIG.EUF_CACHE)

BASE_DIR = str(Path(__file__).parent.parent.absolute())

CONFIG.GOTO_BUILD_SCRIPT = f"{BASE_DIR}/scripts/mk_goto.sh"
CONFIG.PLUGIN = f"{BASE_DIR}/clang-suffix/build/lib/libAddSuffix.so"
CONFIG.INIT_VIM =  f"{BASE_DIR}/scripts/init.lua"
CONFIG.RENAME_LUA = f"{BASE_DIR}/scripts/rename.lua"

CONFIG.NAME_GENERATORS = [
        MacroNameGenerator(
                filepath = "expat/lib/xmltok.c",
                arg = "E",
                global_name_suffixes = [
                    "byteType", "isNameMin", "isNmstrtMin", "byteToAscii", "charMatches"
                ]
        ),
        MacroNameGenerator(
                filepath = "expat/lib/xmltok.c",
                arg = "E",
                global_name_suffixes = [
                    "isName2", "isName3", "isName4", "isNmstrt2", "isNmstrt3",
                    "isNmstrt4", "isInvalid2", "isInvalid3", "isInvalid4"
                ]
        )
]

def get_compile_args(compile_db: cindex.CompilationDatabase,
    filepath: str) -> list[str]:
    ''' Load the compilation configuration for the particular file
    and retrieve the compilation arguments '''
    ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
    if ccmds:
        compile_args                    = list(ccmds[0].arguments)
        # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
        # and add the default linker paths
        return compile_args[1:-1]
    else:
        raise Exception(f"Failed to retrieve compilation instructions for {filepath}")

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
    def new_from_cursor(cls, root_dir: str, cursor: cindex.Cursor):
        return cls(
            filepath    = get_path_relative_to(
                str(cursor.location.file), root_dir
            ),
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
    # The line and col references the _new version_ of the dependency
    invokes_changed_functions: list[str]
    direct_change: bool = True

    @classmethod
    def new_from_cursors(cls, old_root: str, new_root: str,
            old_cursor: cindex.Cursor, new_cursor: cindex.Cursor):
        return cls(
            old = DependencyFunction.new_from_cursor(old_root, old_cursor),
            new = DependencyFunction.new_from_cursor(new_root, new_cursor),
            invokes_changed_functions = []
        )


    def detail(self, pretty: bool = False, brief: bool = False):
        if pretty:
            out =   "\033[31mDirect\033[0m change: " if self.direct_change else \
                    "\033[34mIndirect\033[0m change: "
        else:
            out =   "direct change: " if self.direct_change else \
                    "indirect change: "
        if brief and pretty:
                out += "\033[33m"
        if self.old.name == "":
            out += f"b/{self.new}"
        else:
            out += f"a/{self.old} -> b/{self.new}"
        if brief and pretty:
                out += "\033[0m"

        if len(self.invokes_changed_functions) > 0 and not brief:
            out += self.affected_by(pretty)

        return out

    def affected_by(self,pretty=True) -> str:
        out = ""

        if pretty:
            out += "\nAffected by changes to:"
        else:
            out += "\n affected by changes to:"

        for trans_call in self.invokes_changed_functions:
            out += f"\n\t{trans_call}"
        return out

    def __repr__(self):
        return self.detail()

    def __hash__(self):
        ''' 
        Note that the hash does not consider the `invokes_changed_functions` 
        list. A set will thus only include one copy of each function
        '''
        return hash(hash(self.old) + hash(self.new))

@dataclass(init=True)
class ProjectInvocation:
    function: DependencyFunctionChange
    enclosing_name: str
    filepath: str
    line: int
    col: int

    def brief(self):
        return f"call to {self.function.new} at {self.filepath}:{self.line}:{self.col}"

    def invocation(self):
        return f"{self.filepath}:{self.line}:{self.col}:{self.enclosing_name}()"

    def detail(self):
        return f"call to {self.function}\nat {self.invocation()}"

    def __repr__(self):
        return self.detail()

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

@dataclass(init=True)
class Macro:
    name: str
    arguments: list[str]

    start_line: int
    end_line: int
    data: str = ""

    # This is the line in the stub file (after replacement has taken place)
    # were the expanded macro is located
    # We assume that all expanded macros only occupy one line
    stub_file_call_line: int = -1

    def text(self) -> str:
        if len(self.arguments) == 0:
            return f"#define {self.name} {self.data}"
        else:
            comma_sep_args = ','.join(self.arguments).strip(',')
            return f"#define {self.name}({comma_sep_args}) {self.data}"

@dataclass(init=True)
class IdentifierLocation:
    '''
    This class is equvivalent to clang's SourceLocation
    except that it only contains simple properties
    and can thereby be hashed
    '''
    line: int
    column: int
    filepath: str
    name: str


    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor):
        return cls(
                line = cursor.location.line,
                column = cursor.location.column,
                filepath = str(cursor.location.file),
                name = cursor.spelling
        )

    def __repr__(self) -> str:
        brief_path = compact_path(CONFIG.EUF_CACHE) + remove_prefix(self.filepath, CONFIG.EUF_CACHE)
        return f"{brief_path}:{self.name}:{self.line}:{self.column}"

    def to_csv(self) -> str:
        return f"{self.filepath};{self.name};{self.line};{self.column}"


    def __hash__(self):
        return hash(str(self.line)+str(self.column)+str(self.filepath)+self.name)
