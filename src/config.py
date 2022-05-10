import os, json, multiprocessing
from dataclasses import dataclass, field
from src import BASE_DIR

def _parse_path(value) -> str:
    if value != "":
        return os.path.abspath(os.path.expanduser(value))
    return ""

@dataclass
class Config:
    ''' - - - Obligatory fields - - - '''
    # .git directory of the main project being analyzed
    _PROJECT_DIR: str = ""

    # .git directory of the dependency being analyzed
    #
    # This directory is only used when:
    #   1. Creating Repo() objects
    #   2. Working with paths given from git.Diff objects which
    #   are relative to the .git root
    # In all other situations the DEP_SOURCE_ROOT is used
    _DEPENDENCY_DIR: str = ""

    # The 'project' directory of the dependency being analyzed
    # in which compile_commands.json is created
    # default: same as .git directory
    _DEP_SOURCE_ROOT: str = ""

    # Name of the library to analyze, e.g. libonig.a
    DEPLIB_NAME: str = ""

    # Git hash of the new version of the dependency
    COMMIT_NEW: str = ""

    # Git hash of the old (current) version of the dependency
    COMMIT_OLD: str = ""

    #  - - - - - - - - - - - - - - - - - -
    # Paths to exclude from all analysis, given as a list
    # of regular expressions
    EXCLUDE_REGEXES: list[str] = field(default_factory=list)

    # Using 0 will suppress all output except
    # the impact summary and certain errors,
    # -1 and lower will suppress the impact summary
    VERBOSITY: int = 0

    # Impact set output format
    ORDER_BY_CALL_SITE: bool = True

    # Show diff of files in the change set and exit
    SHOW_DIFFS: bool = False

    # Name of a specific function to limit analysis during debugging
    ONLY_ANALYZE: str = ""

    # Skip the blame correlation performed during the git-diff stage
    SKIP_BLAME: bool = False

    # Skip call site correlation (exit after CBMC analysis)
    SKIP_IMPACT: bool = False

    # Log information from each stage to .csv files under RESULTS_DIR
    ENABLE_RESULT_LOG: bool = True

    # Number of times to look for indirect changes by finding all functions
    # that call a function with direct or indirect change
    TRANSATIVE_PASSES: int = 1

    # Wait for <Enter> to be pressed before continuing at each stage
    PAUSES: bool = False

    # - - - Harness generation  - - -
    # System header paths to skip over for the #include directives
    # of the driver
    SKIP_HEADERS_UNDER: list[str] = field(default_factory=lambda: [
        "include/bits",
        "include/x86_64-linux-gnu",
        "lib/clang",
        "include/clang/13.0.0",

        "local/lib/clang",
        "local/include/bits",
    ])

    # These prefixes will be removed from headers that are included
    # with #include <...>
    SYSTEM_INCLUDE_PREFIXES: list[str] = field(default_factory=lambda: [
        "/usr/lib", "/usr/local/include", "/usr/include"
    ])

    # A list of strings that should be explicitly given a
    # suffix in the old version of the library
    #
    # This can be useful in scenarios were a struct has
    # renamed fileds, causing conflicts unless the struct is split
    # into two different versions
    #
    # Renaming types can also have other side effects that cause
    # failed compilation
    EXPLICIT_RENAME: list[str] = field(default_factory=list)

    # Some projects will declare types inside source files rather
    # than in header files (libexpat and libonig).
    # If these types are needed as arguments to a
    # function in a driver we need some way of including them
    # The current solution is to provide a custom header
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
    #      "exact_include_directive_without_abs_path"
    #   ]
    #
    # EUF will differentiate between the two cases based on if
    # the value is an existent file or not
    CUSTOM_HEADERS: dict[str,list[str]] = field(default_factory=dict)

    # Expat has certain headers which work more like macro definitions
    # If we include these headers like normal headers we get syntax
    # errors and it is therefore necessary to blacklist them
    BLACKLISTED_HEADERS: list[str] = field(default_factory=list)

    # - - - Building - - -
    # Environment variables to set when running `./configure`
    # It is not necessary to pass `-fvisibility=default` here to access
    # all functions, the CBMC fork is configured to make
    # changed static functions accessible outside of their TU automatically
    BUILD_ENV: dict[str,str] = field(default_factory=dict)

    # Set to True to echo out all information during the build process
    # of the ccdb and the goto libs
    QUIET_BUILD: bool = True

    # Remove all existing GOTO-bin libraries and recompile them
    FORCE_RECOMPILE: bool = False

    # Attempt to re-create the compile_commands.json for each dependency
    # version and the main project.
    # Note: This will only delete an existing ccdb if EUF is able to
    # auto-generate a new version,  manually created ccdbs
    # for e.g. Cmake projects will thus not be removed.
    FORCE_CCDB_RECOMPILE: bool = False

    # - - - CBMC analysis - - -
    # False to skip all CBMC analysis
    FULL: bool = False

    # Suppress all output from CBMC during ID analysis and/or the main analysis
    SILENT_IDENTITY_VERIFICATION: bool = True
    SILENT_VERIFICATION: bool = True

    # Functions for which no CBMC analysis should be attempted
    IGNORE_FUNCTIONS: list[str] = field(default_factory=lambda: [
            "main"
    ])

    # Show part of the GOTO functions before running CBMC analysis
    # ** NOTE: Overriden by SILENT_VERIFICATION **
    SHOW_FUNCTIONS: bool = False

    # If set to True, successful verifications will
    # remove an item from the change set even if
    # --unwinding-assertions generated a failure
    REDUCE_INCOMPLETE_UNWIND: bool = True

    # Perform full analysis regardless of if the identity analysis
    # is successful
    IGNORE_FAILED_IDENTITY: bool = False

    # Options for each cbmc invocation
    CBMC_OPTS_STR: str = \
        "--object-bits 12 --unwind 1 --unwinding-assertions --havoc-undefined-functions"

    # Stop execution if a harness cannot be executed or compiled due to errors
    DIE_ON_ERROR: bool = False

    # The timeout (seconds) before killing CBMC analysis
    CBMC_TIMEOUT: int = 60

    # Do not generate a new driver if one already exists under .harnesses.
    # This allows for manual modifications and provisioning of custom drivers
    USE_EXISTING_DRIVERS: bool = False


    # Functions listed in this file will be skipped during analysis
    # Any function that receives a TIMEOUT result will be
    # automatically appended to the file
    TIMEOUT_BLACKLIST_FILE: str = f"{BASE_DIR}/blacklist.txt"
    ENABLE_TIMEOUT_BLACKLIST: bool = False

    # - - - Internal - - -
    # A file will be considered renamed if git blame only finds
    # two origins for changes and the changes are within the ratio
    # [0.5,RENAME_RATIO_LOW]
    RENAME_RATIO_LOW: float = .3

    # Generate warnings when inconsistent parameter usage is detected
    # based on the type field of clang AST nodes
    # This usually produces a lot of FPs e.g. char_s != char_u
    STRICT_TYPECHECKS: bool = False

    LIBCLANG: str = "/usr/lib/libclang.so.13.0.1"
    LIBCLANG_FALLBACKS: list[str] = field(default_factory=lambda:[
        "/usr/local/lib/libclang.so.13.0.1",
        "/usr/lib/llvm-13/lib/libclang.so.1"
    ])

    # Extra compile flags to add for every TU in libclang
    # NOTE: This applies both for the main project AND dependencies
    # there is currently no interface for providing different
    # extra options
    EXTRA_COMPILE_FLAGS = []

    # Compilation flag patterns to exclude from invocations of
    # the ArgStates clang-plugin, NOTE this can remove entries defined
    # in EXTRA_COMPILE_FLAGS.
    ARG_STATES_COMPILE_FLAG_BLACKLIST = [
        "-g", "-c", r"-f.*"
    ]

    # File suffixes to consider during the git diffing stage
    SUFFIX_WHITELIST_GIT_DIFF = [".c", ".h"]

    # Only these suffixes will be considered for any type of analysis,
    # besides git diff.
    # Attempts were made to support .h files (using compdb) but the feature
    # was deemed to unstable to include support for it.
    SUFFIX_WHITELIST = [".c"]

    UNRESOLVED_NODES_REGEX: str = r"unnamed at|<dependent type>"

    # Compiler used during ccdb generation and invocations
    # of the ArgStates plugin
    CCDB_CC = "/usr/bin/clang"
    NPROC: int = max(1,multiprocessing.cpu_count() - 1)

    # The location to store the new version of the dependency
    EUF_CACHE: str = f"{os.path.expanduser('~')}/.cache/euf"
    HARNESS_DIR: str = ".harnesses"
    OUTDIR: str = f"{BASE_DIR}/.out"
    RESULTS_DIR: str = f"{BASE_DIR}/results"
    CBMC_SCRIPT: str = f"{BASE_DIR}/scripts/cbmc_driver.sh"
    RENAME_CSV: str = "/tmp/rename.csv"
    CBMC_OUTFILE: str = "runner"
    EUF_ENTRYPOINT: str = "euf_main"
    IDENTITY_HARNESS: str = "_id"
    INDENT: str = " "*2
    CLANG_PLUGIN_RUN_STR_LIMIT: int = 1000

    ARG_STATS_SO=f"{BASE_DIR}/clang-plugins/build/lib/libArgStates.so"

    # !! DO NOT CHANGE, hardcoded in ./scripts/cbmc_driver.sh !!
    CBMC_ASSERT_MSG: str = "Equivalent output"

    # Print debug information when running ArgStates.so
    DEBUG_CLANG_PLUGIN: bool = False

    # !! DO NOT CHANGE, hardcoded in clang plugin !!
    ARG_STATES_OUT_DIR_ENV = "ARG_STATES_OUT_DIR"
    ARG_STATES_DEBUG_ENV = "DEBUG_AST"
    ARG_STATES_OUTDIR = f"{BASE_DIR}/.states"

    # !! DO NOT CHANGE, hardcoded in CBMC fork !!
    SUFFIX: str = "_old_b026324c6904b2a"
    RENAME_TXT: str = "/tmp/rename.txt"
    SUFFIX_ENV_FLAG: str = "USE_SUFFIX"

    # - - - Property setters

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
        self._PROJECT_DIR = _parse_path(value)
    @DEPENDENCY_DIR.setter
    def DEPENDENCY_DIR(self,value):
        self._DEPENDENCY_DIR = _parse_path(value)
    @DEP_SOURCE_ROOT.setter
    def DEP_SOURCE_ROOT(self,value):
        self._DEP_SOURCE_ROOT = _parse_path(value)

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
        Reinitialize with default values, used to avoid
        inconsistencies during tests
        '''
        default = Config()
        for attr in dir(self):
            # Only assign values to members in capital letters
            if not attr.startswith("__") and attr.upper() == attr:
                setattr(self, attr, getattr(default,attr))

CONFIG = Config()


