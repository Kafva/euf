from enum import Enum
import re
import sys, os, json
from pathlib import Path
from dataclasses import dataclass, field
from clang import cindex

# Enable importing from the root directory inside the module
sys.path.append('../')

BASE_DIR = str(Path(__file__).parent.parent.absolute())

def get_path_relative_to(path: str, base: str) -> str:
    return path.removeprefix(base).removeprefix("/")

def compact_path(path: str) -> str:
    out = ""
    for name in path.split("/"):
        if len(name) >= 2 and not name[0].isalnum():
            out += "/" + name[:2]
        elif len(name) > 0:
            out += "/" + name[0]

    return out

class AnalysisResult(Enum):
    SUCCESS = 0 # SUCCESS verification: equivalent change
    ERROR = 1
    INTERRUPT = 51
    TIMEOUT = 52
    # "SUCCESS": No verification conditions generated
    NO_VCCS = 53
    # FAILED verification: non-equivalent change
    FAILURE = 54

@dataclass
class Config:
    # - - - General - - -
    _PROJECT_DIR: str = ""
    _DEPENDENCY_DIR: str = ""
    _DEP_SOURCE_ROOT: str = ""
    DEPLIB_NAME: str = ""
    COMMIT_NEW: str = ""
    COMMIT_OLD: str = ""

    TRANSATIVE_PASSES: int = 1
    NPROC: int = 5
    LIBCLANG: str = "/usr/lib/libclang.so.13.0.1"

    # Paths to exclude from all analysis (requires a '*'
    # to match all files under a directory)
    EXCLUDE_REGEXES: list[str] = field(default_factory=list)

    # Impact set output format
    REVERSE_MAPPING: bool = False

    # Show diffs of files in change set and exit
    SHOW_DIFFS: bool = False

    # - - - Verbosity  - - -
    VERBOSITY: int = 0

    # Name of a specific function to limit analysis during debugging
    ONLY_ANALYZE: str = ""
    SILENT_IDENTITY_VERIFICATION: bool = True

    SKIP_BLAME: bool = False
    SKIP_IMPACT: bool = False
    ENABLE_RESULT_LOG: bool = False

    # Functions for which no CBMC analysis should be attempted
    IGNORE_FUNCTIONS: list[str] = field(default_factory=lambda: ["main"])

    # Show part of the goto functions before running CBMC analysis
    SHOW_FUNCTIONS: bool = False

    # - - - Building - - -
    # Environment variables to set when running `./configure`
    # during ccdb generation and goto-bin compilation
    # This will usually involve setting CFLAGS and/or CPPFLAGS to override
    # specific default values set in AM_CFLAGS and AM_CPPFLAGS 
    #
    # It is not necessary to pass `-fvisibility=default` to access
    # all functions, the CBMC fork is configured to make functions
    # accessible outside of their TU
    BUILD_ENV: dict[str,str] = field(default_factory=dict)
    FORCE_RECOMPILE: bool = False

    _GOTO_BUILD_SCRIPT: str = ""
    _CCDB_BUILD_SCRIPT: str = ""

    # List of include paths used by the old version of the dependency
    DEP_INCLUDE_PATHS: list[str] = field(default_factory=list)

    # System header paths to skip over for the #include directives
    # of the driver
    SKIP_HEADERS_UNDER: list[str] = field(default_factory=lambda: ["bits"])

    # Set to True to echo out all information during the build process
    # of the ccdb and the goto libs
    QUIET_BUILD: bool = True

    # Some projects will declare types inside source files rather
    # than in header files. If these types are needed as arguments to a
    # function in a driver we need some way of including them
    # Currently, we simply provide the option of giving a custom header
    # with the neccessary definitions to resolve this
    #
    # Format:
    #   src_file: [
    #       "custom.h"
    #    ]
    CUSTOM_HEADERS: dict[str,list[str]] = field(default_factory=dict)

    # - - - CBMC - - -
    FULL: bool = False # False to skip all CBMC analysis
    CBMC_OPTS_STR: str = "--object-bits 12 --unwind 10"
    DIE_ON_ERROR: bool = False

    # The timeout (seconds) before killing CBMC analysis
    CBMC_TIMEOUT: int = 60

    # Maps function names to filepaths of drivers
    DRIVERS: dict[str,str] = field(default_factory=dict)

    # Override to only use a specific (provided) driver for CBMC
    USE_PROVIDED_DRIVER: bool = False

    # - - - Internal - - -
    # A file will be considered renamed if git blame only finds
    # two origins for changes and the changes are within the ratio
    # [0.5,RENAME_RATIO_LOW]
    RENAME_RATIO_LOW: float = .3

    # Only used during ccdb generation
    TARGET_TRIPLET: str = "x86_64-unknown-linux"

    # The location to store the new version of the dependency
    EUF_CACHE: str = f"{os.path.expanduser('~')}/.cache/euf"
    HARNESS_DIR: str = ".harnesses"
    OUTDIR: str = f"{BASE_DIR}/.out"
    RESULTS_DIR: str = f"{BASE_DIR}/results"
    CBMC_SCRIPT: str = f"{BASE_DIR}/scripts/cbmc_driver.sh"
    RENAME_CSV: str = "/tmp/rename.csv"
    CBMC_OUTFILE: str = "runner"
    EUF_ENTRYPOINT: str = "euf_main"
    CBMC_ASSERT_MSG: str = "Equivalent output"
    IDENTITY_HARNESS: str = "_id"
    INDENT: str = " "*2

    # !! DO NOT CHANGE, hardcoded in CBMC fork !!
    SUFFIX: str = "_old_b026324c6904b2a"
    RENAME_TXT: str = "/tmp/rename.txt"
    SUFFIX_ENV_FLAG: str = "USE_SUFFIX"

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
            'DEPLIB_NAME': self.DEPLIB_NAME,
            'SHOW_FUNCTIONS': str(self.SHOW_FUNCTIONS).lower()
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
    def GOTO_BUILD_SCRIPT(self) -> str:
        return self._GOTO_BUILD_SCRIPT
    @property
    def CCDB_BUILD_SCRIPT(self) -> str:
        return self._CCDB_BUILD_SCRIPT

    @PROJECT_DIR.setter
    def PROJECT_DIR(self,value):
        self._PROJECT_DIR = self._parse_path(value)
    @DEPENDENCY_DIR.setter
    def DEPENDENCY_DIR(self,value):
        self._DEPENDENCY_DIR = self._parse_path(value)
    @DEP_SOURCE_ROOT.setter
    def DEP_SOURCE_ROOT(self,value):
        self._DEP_SOURCE_ROOT = self._parse_path(value)
    @GOTO_BUILD_SCRIPT.setter
    def GOTO_BUILD_SCRIPT(self,value):
        self._GOTO_BUILD_SCRIPT = self._parse_path(value)
    @CCDB_BUILD_SCRIPT.setter
    def CCDB_BUILD_SCRIPT(self,value):
        self._CCDB_BUILD_SCRIPT = self._parse_path(value)

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
class Identifier:
    ''' 
    Refers to either a function argument or a function, 
    '''
    spelling: str
    type_spelling: str # Includes a '*' if the ident is a ptr

    # The type is a string conversions from `cindex.TypeKind`
    # If the object refers to a function, the type reflects the return type
    typing: str

    # If set, the identifier is a pointer to the specified type
    is_ptr: bool = False
    is_const: bool = False
    is_function: bool = False

    def __repr__(self, paranthesis: bool = True):
        constant = 'const ' if self.is_const else ''
        func = '()' if self.is_function and paranthesis else ''
        return f"{constant}{self.type_spelling} {self.spelling}{func}"

    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor):
        is_function = str(cursor.type.kind).endswith("FUNCTIONPROTO")

        # For functions we are intrested in the `.result_type`, this value
        # is empty for function arguments which instead 
        # have their typing in `.type`
        type_obj = cursor.result_type if is_function else cursor.type

        result_pointee_type = type_obj.get_pointee()

        if result_pointee_type.spelling != "":
            # Pointer return type
            typing = str(result_pointee_type.kind) \
                    .removeprefix("TypeKind.").lower()
            type_spelling = str(result_pointee_type.spelling) \
                .removeprefix("const ")
            is_const = result_pointee_type.is_const_qualified()
            is_ptr = True
        else:
            typing = str(type_obj.kind) \
                    .removeprefix("TypeKind.").lower()
            type_spelling = str(type_obj.spelling) \
                    .removeprefix("const ")
            is_const = type_obj.is_const_qualified()
            is_ptr = False

        if re.search(r"^int\**", type_spelling):
            type_spelling = cls.get_type_from_text(cursor, type_spelling)

        return cls(
            spelling = cursor.spelling,
            typing = typing,
            type_spelling = type_spelling + ('*' if is_ptr else ''),
            is_ptr = is_ptr,
            is_const = is_const,
            is_function = is_function
        )

    @classmethod
    def get_type_from_text(cls, cursor: cindex.Cursor, type_spelling: str) -> str:
        '''
        ~~~ Hack ~~~
        Built-in typedefs like size_t do not get resolved properly
        and we resolve them by looking in the actual source file
        '''
        try:
            with open(str(cursor.location.file), mode='r', encoding='utf8') as f:
                lines = f.readlines()

                # Get the line of the identifier
                line_offset = cursor.location.line-1
                line = lines[line_offset]

                # Retrieve the text before the identifier on the same line
                before_ident = line[:cursor.location.column-1]

                # We assume that there are no more than 5 newlines
                # between the identifier and the type specifier
                low = max(line_offset-4,0)
                high = max(line_offset-1,0)
                before_ident = ' '.join(lines[low:high]) \
                        + before_ident
                before_ident = before_ident.replace('\n', ' ')

                if (match := re.match(r".*,\s*([_0-9a-zA-Z]+)\s*$", before_ident)):
                    type_spelling = match.group(1)
        except UnicodeDecodeError:
            # Oniguruma has some source files with exotic encodings
            pass

        return type_spelling

    @classmethod
    def empty(cls):
        return cls(
            spelling="",
            typing="",
            type_spelling=""
        )

    def __eq__(self, other) -> bool:
        ''' 
        Does not consider nodes which only differ in spelling
        as different
        '''
        return self.type_spelling == other.type_spelling and \
               self.typing == other.typing and self.is_ptr == other.is_ptr and \
               self.is_function == other.is_function and \
               self.is_const == other.is_const

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
    ident: Identifier # Function name and return type
    displayname: str # Includes the full prototype string
    filepath: str
    arguments: list[Identifier]
    line: int
    col: int

    @classmethod
    def new_from_cursor(cls, root_dir: str, cursor: cindex.Cursor):
        return cls(
            filepath    = get_path_relative_to(
                str(cursor.location.file), root_dir
            ),
            displayname = cursor.displayname,
            ident        = Identifier.new_from_cursor(cursor) ,
            arguments   = [ Identifier.new_from_cursor(arg)
                  for arg in cursor.get_arguments() ],
            line = cursor.location.line,
            col = cursor.location.column
        )

    @classmethod
    def empty(cls):
        return cls(
            filepath    = "",
            displayname = "",
            ident       = Identifier.empty(),
            arguments   = [],
            line = 0,
            col = 0
        )

    def __repr__(self):
        return f"{self.filepath}:{self.line}:{self.col}:{self.ident.spelling}()"

    def prototype_string(self, suffix: str = "") -> str:
        out = f"{self.ident.__repr__(paranthesis=False)}{suffix}("
        for arg in self.arguments:
            out += f"{arg}, "

        return out.removesuffix(", ") + ")"

    def __hash__(self):
        return hash(self.filepath + self.ident.__repr__() + self.displayname +
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
        if self.old.ident.spelling == "":
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

    def to_csv(self) -> str:
        return f"{self.direct_change};{self.old.filepath};{self.old.ident.spelling};{self.old.line};{self.old.col};" + \
                f"{self.new.filepath};{self.new.ident.spelling};{self.new.line};{self.new.col}"

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
        brief_path = compact_path(CONFIG.EUF_CACHE) + self.filepath.removeprefix(CONFIG.EUF_CACHE)
        return f"{brief_path}:{self.name}:{self.line}:{self.column}"

    def to_csv(self) -> str:
        return f"{self.filepath};{self.name};{self.line};{self.column}"


    def __hash__(self):
        return hash(str(self.line)+str(self.column)+str(self.filepath)+self.name)
