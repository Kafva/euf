import os, json
from src import BASE_DIR
from dataclasses import dataclass, field

@dataclass
class Config:
    ''' - - - General - - - '''
    _PROJECT_DIR: str = ""
    _DEPENDENCY_DIR: str = ""
    _DEP_SOURCE_ROOT: str = ""
    DEPLIB_NAME: str = ""
    COMMIT_NEW: str = ""
    COMMIT_OLD: str = ""

    TRANSATIVE_PASSES: int = 1
    NPROC: int = 5
    LIBCLANG: str = "/usr/lib/libclang.so.13.0.1"
    FALLBACK_LIBCLANG: str = "/usr/local/lib/libclang.so.13.0.1"

    # Paths to exclude from all analysis (requires a '*'
    # to match all files under a directory)
    EXCLUDE_REGEXES: list[str] = field(default_factory=list)

    # Impact set output format
    ORDER_BY_CALL_SITE: bool = True

    # Show diffs of files in change set and exit
    SHOW_DIFFS: bool = False

    # A list of strings that should be explicitly given a 
    # suffix in the old version of the library
    #
    # This is useful in scenarios were e.g. a struct has
    # function pointer fields (which are renamed), causing
    # conflicts unless the struct is split into two different 
    # versions (see usb_os_backend in libusb).
    #
    # Note that renaming types is only viable if the type in
    # in question never appears as a function parameter or return value
    EXPLICIT_RENAME: list[str] = field(default_factory=list)

    # - - - Verbosity  - - -
    VERBOSITY: int = 0

    # Wait for <Enter> to be pressed before continuing at each stage
    PAUSES: bool = False

    # Name of a specific function to limit analysis during debugging
    ONLY_ANALYZE: str = ""

    SILENT_IDENTITY_VERIFICATION: bool = False
    SILENT_VERIFICATION: bool = False

    SKIP_BLAME: bool = False
    SKIP_IMPACT: bool = False
    ENABLE_RESULT_LOG: bool = True

    # Functions for which no CBMC analysis should be attempted
    IGNORE_FUNCTIONS: list[str] = field(default_factory=lambda: ["main"])

    # Show part of the goto functions before running CBMC analysis
    # ** NOTE: Overriden by SILENT_VERIFICATION **
    SHOW_FUNCTIONS: bool = False

    # Generate warnings when inconsistent parameter usage is detected
    # based on the type field of clang AST nodes
    # This usually produces a lot of FPs e.g. char_s != char_u
    STRICT_TYPECHECKS: bool = False

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
    FORCE_CCDB_RECOMPILE: bool = False

    # System header paths to skip over for the #include directives
    # of the driver
    SKIP_HEADERS_UNDER: list[str] = field(default_factory=lambda:
            ["include/bits", "lib/clang"]
    )

    # Extra compile flags to add for every TU in libclang
    EXTRA_COMPILE_FLAGS = [
        "-Wno-unused-function"
    ]

    # Set to True to echo out all information during the build process
    # of the ccdb and the goto libs
    QUIET_BUILD: bool = True

    # Some projects will declare types inside source files rather
    # than in header files (libexpat and libonig). 
    # If these types are needed as arguments to a
    # function in a driver we need some way of including them
    # Currently, we simply provide the option of giving a custom header
    # with the necessary definitions to resolve this
    #
    # Format:
    #   src_file: [
    #       "/path/to/custom.h"
    #    ]
    #
    # If libclang fails to include a header that a TU actually uses,
    # a header entry can be provided in this array on the form
    #
    #   src_file: [
    #      "exact_include_directive" 
    #   ]
    #
    # EUF will differentiate between the two cases based on if the
    # the value is existant file or not
    CUSTOM_HEADERS: dict[str,list[str]] = field(default_factory=dict)

    # Expat has certain headers which work more like macro definitions
    # If we include these headers like normal headers we get syntax
    # errors and it is therefore neccessary to blacklist them
    BLACKLISTED_HEADERS: list[str] = field(default_factory=list)

    # - - - CBMC - - -
    FULL: bool = False # False to skip all CBMC analysis
    CBMC_OPTS_STR: str = "--object-bits 12 --unwind 10"
    DIE_ON_ERROR: bool = False

    # The timeout (seconds) before killing CBMC analysis
    CBMC_TIMEOUT: int = 60

    # Do not generate a new driver if one already exists under .harnesses
    # allows for manual modifications and custom drivers to be provided
    USE_EXISTING_DRIVERS: bool = False

    # - - - Internal - - -
    # A file will be considered renamed if git blame only finds
    # two origins for changes and the changes are within the ratio
    # [0.5,RENAME_RATIO_LOW]
    RENAME_RATIO_LOW: float = .3

    # Only files with these suffixes are considered during analysis
    SUFFIX_WHITELIST = [".c", ".h"]

    UNRESOLVED_NODES_REGEX: str = r"unnamed at|<dependent type>"

    # Compiler used during ccdb generation
    CCDB_CC = "cc"

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

    # Compilation flag patterns to exclude from invocations of 
    # clang-plugins/ArgStates
    ARG_STATES_COMPILE_FLAG_BLACKLIST = ["-g", "-c", r"-f.*", r"-W.*"]
    ARG_STATS_SO=f"{BASE_DIR}/clang-plugins/build/lib/libArgStates.so"

    # !! DO NOT CHANGE, hardcoded in clang plugin !!
    ARG_STATES_OUT_DIR_ENV = "ARG_STATES_OUT_DIR"
    ARG_STATES_DEBUG_ENV = "DEBUG_AST"
    ARG_STATES_OUTDIR = f"{BASE_DIR}/.states"

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
        script_env = os.environ.copy() # This is neccessary for clang
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

    @PROJECT_DIR.setter
    def PROJECT_DIR(self,value):
        self._PROJECT_DIR = self._parse_path(value)
    @DEPENDENCY_DIR.setter
    def DEPENDENCY_DIR(self,value):
        self._DEPENDENCY_DIR = self._parse_path(value)
    @DEP_SOURCE_ROOT.setter
    def DEP_SOURCE_ROOT(self,value):
        self._DEP_SOURCE_ROOT = self._parse_path(value)

    def update_from_file(self, filepath: str):
        ''' If we create a new object the CONFIG object wont be shared '''
        self.reset()
        with open(filepath, mode = "r", encoding = "utf8") as f:
           dct = json.load(f)
           for key,val in dct.items():
            if key in dct:
                setattr(self, key, val) # Respects .setters

    def reset(self):
        '''
        Reinitalize with default values, used to avoid
        inconsistcies during tests
        '''
        default = Config()
        for attr in dir(self):
            # Only assign values to memebers in capital letters
            if not attr.startswith("__") and attr.upper() == attr:
                setattr(self, attr, getattr(default,attr))

CONFIG = Config()


