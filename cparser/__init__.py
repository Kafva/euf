import sys, os, json
from pathlib import Path
from dataclasses import dataclass, field
from clang import cindex
from cparser.util import compact_path, get_path_relative_to, remove_prefix

# Enable importing from the root directory inside the module
sys.path.append('../')

BASE_DIR = str(Path(__file__).parent.parent.absolute())

@dataclass
class Config:
    ''' - - - CLI options  - - - '''
    _PROJECT_DIR: str = ""
    _DEPENDENCY_DIR: str = ""
    _DEP_SOURCE_ROOT: str = ""
    DEPLIB_NAME: str = ""
    COMMIT_NEW: str = ""
    COMMIT_OLD: str = ""

    VERBOSITY: int = 0
    NPROC: int = 5
    UNWIND: int = 1
    OBJECT_BITS: int = 12
    FULL: bool = False
    FORCE_RECOMPILE: bool = False
    SKIP_BLAME: bool = False
    SKIP_IMPACT: bool = False

    LIBCLANG: str = "/usr/lib/libclang.so.13.0.1"

    _RENAME_BLACKLIST: str = ""
    _GOTO_BUILD_SCRIPT: str = ""
    _CCDB_BUILD_SCRIPT: str = ""
    _RENAME_SCRIPT: str = ""
    PLUGIN: str = f"{BASE_DIR}/clang-suffix/build/lib/libAddSuffix.so"

    # - - - Internal - - -
    # A file will be considered renamed if git blame only finds
    # two origins for changes and the changes are within the ratio
    # [0.5,RENAME_RATIO_LOW]
    RENAME_RATIO_LOW: float = .3
    TRANSATIVE_PASSES: int = 1

    # The location to store the new version of the dependency
    EUF_CACHE: str = f"{os.path.expanduser('~')}/.cache/euf"
    CACHE_INTERNAL_STASH: str = "INTERNAL EUF STASH"
    OUTDIR: str = f"{BASE_DIR}/.out"
    SUFFIX: str = "_old_b026324c6904b2a" # DO NOT CHANGE, hardcoded in CBMC fork
    REVERSE_MAPPING: bool = False

    # Toggles echoing of scripts
    SETX: str = "false"

    INIT_VIM: str = f"{BASE_DIR}/scripts/init.lua"
    RENAME_LUA: str = f"{BASE_DIR}/scripts/rename.lua"

    # Reuse /tmp/rename.txt if present
    REUSE_EXISTING_NAMES: bool = False
    RENAME_CSV: str = "/tmp/rename.csv" # DO NOT CHANGE, hardcoded in CBMC fork
    NVIM: str = "/usr/bin/nvim"
    EUF_NVIM_SOCKET: str = "/tmp/eufnvim"
    CBMC_OUTFILE: str = "runner"
    EUF_ENTRYPOINT: str = "euf_main"

    EDIT_DELAY: float = 2
    REQUIRED_HEADERS: list[str] = field(default_factory=list)

    '''
    Expat has a 'noop' macro on the form
        #define NS(x) x

    CCLS cannot rename declerations on the form (even if we have the cursor on 'foo')
        void NS(foo) (int arg);

    The same occurs for PREFIX() (which has the additional complication of 
    manipulating the actual function name)

    To exclude replacement steps for these cases we check if the cursor is on 'NS('
    before doing any replacements (we cant sieve out these entries eariler since they dont have a prefix)
    The dicts in this object are on the form 
		{
            "name": "PREFIX",
            "prefixes": [ "little2_", "normal_", "big2_" ]
		}
    To simplify the config file parsing we dont use a class for this
    '''
    MACRO_NAMES: list[dict[str,str|list[str]]] = field(default_factory=list)

    # Maps function names to filepaths of drivers
    DRIVERS: dict[str,str] = field(default_factory=dict)

    # Override to only use a specific (provided) driver for CBMC
    USE_PROVIDED_DRIVER: bool = False

    # Not all functions defined in a library are visible to our driver if the
    # authors of the library have used the `-fvisibility=hidden` flag during compilation
    # This flag removes any functions that are not explicitly marked as visible from
    # the symbol table. We need it to be set to 'default' to make everything visible (`man gcc`)
    #
    # However, if a function lacks a decleration in a header file it will still
    # be rendered unexported so we need to manually ensure that all functions
    # we want to test have a decleration in the main header of the library
    #
    # Furthermore, we need to drop the `static` specificer from any functions
    # that use it since static functions are bound to a single TU
    # This can cause issues when a static function expects a global to be
    # present.

    # Enviroment varaibles to set when running `./configure`
    # during ccdb generation and goto-bin compliation
    # This will usually involve setting CFLAGS and/or CPPFLAGS to override
    # specific default values set in AM_CFLAGS and AM_CPPFLAGS
    BUILD_ENV: dict[str,str] = field(default_factory=dict)


    # - - - Property setters
    def _parse_path(self, value) -> str:
        if value != "":
            return os.path.abspath(os.path.expanduser(value))
        else:
            return ""

    def get_script_env(self) -> dict:
        '''
        All custom shell scripts invoked by EUF will 
        have (at least) these values available
        '''
        script_env = os.environ.copy()
        script_env.update({
            'DEPENDENCY_DIR': self.DEPENDENCY_DIR,
            'DEP_SOURCE_ROOT': self.DEP_SOURCE_ROOT,
            'SUFFIX': self.SUFFIX,
            'PROJECT_DIR': self.PROJECT_DIR,
            'SETX': self.SETX,
            'DEPLIB_NAME': self.DEPLIB_NAME
        })

        return script_env

    @property
    def PROJECT_DIR(self) -> str:
        return self._PROJECT_DIR
    @property
    def DEPENDENCY_DIR(self) -> str:
        return self._DEPENDENCY_DIR
    @property
    def DEP_SOURCE_ROOT(self) -> str:
        return self._DEP_SOURCE_ROOT
    @property
    def RENAME_BLACKLIST(self) -> str:
        return self._RENAME_BLACKLIST
    @property
    def GOTO_BUILD_SCRIPT(self) -> str:
        return self._GOTO_BUILD_SCRIPT
    @property
    def CCDB_BUILD_SCRIPT(self) -> str:
        return self._CCDB_BUILD_SCRIPT
    @property
    def RENAME_SCRIPT(self) -> str:
        return self._RENAME_SCRIPT

    @PROJECT_DIR.setter
    def PROJECT_DIR(self,value):
        self._PROJECT_DIR = self._parse_path(value)
    @DEPENDENCY_DIR.setter
    def DEPENDENCY_DIR(self,value):
        self._DEPENDENCY_DIR = self._parse_path(value)
    @DEP_SOURCE_ROOT.setter
    def DEP_SOURCE_ROOT(self,value):
        self._DEP_SOURCE_ROOT = self._parse_path(value)
    @RENAME_BLACKLIST.setter
    def RENAME_BLACKLIST(self,value):
        self._RENAME_BLACKLIST = self._parse_path(value)
    @GOTO_BUILD_SCRIPT.setter
    def GOTO_BUILD_SCRIPT(self,value):
        self._GOTO_BUILD_SCRIPT = self._parse_path(value)
    @CCDB_BUILD_SCRIPT.setter
    def CCDB_BUILD_SCRIPT(self,value):
        self._CCDB_BUILD_SCRIPT = self._parse_path(value)
    @RENAME_SCRIPT.setter
    def RENAME_SCRIPT(self,value):
        self._RENAME_SCRIPT = self._parse_path(value)

    def update_from_file(self, filepath: str):
        ''' If we create a new object the CONFIG object wont be shared '''
        with open(filepath, mode = "r", encoding = "utf8") as f:
           dct = json.load(f)
           for key,val in dct.items():
            if key in dct:
                setattr(self, key, val) # Respects .setters

global CONFIG
CONFIG = Config()

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
