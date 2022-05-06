import re, subprocess, traceback, os
from dataclasses import dataclass, field
from enum import Enum

from clang import cindex
from src import ERR_EXIT
from src.config import CONFIG

class AnalysisResult(Enum):
    SUCCESS = 0 # SUCCESS verification: equivalent change
    ERROR = ERR_EXIT
    # SUCCESS verification of equivalent change and failed unwinding assertion
    SUCCESS_UNWIND_FAIL = 73
    # FAILED verification and failed unwinding assertion
    FAILURE_UNWIND_FAIL = 74
    INTERRUPT = 51
    TIMEOUT = 52
    # "SUCCESS": No verification conditions generated
    NO_VCCS = 53
    # FAILED verification: non-equivalent change
    FAILURE = 54
    # Inconclusive: One or both of the functions to test lacks a body
    NO_BODY = 55
    # Occurs if a struct has a different number of fields in the old/new update
    STRUCT_CNT_CONFLICT = 63
    # Occurs if a struct has a different types for fields in the old/new update
    STRUCT_TYPE_CONFLICT = 64

    # Failed pre-analysis checks
    VOID_RET = 56
    VOID_ARG = 57
    NO_ARGS = 58
    DIFF_RET = 59
    DIFF_ARG_CNT = 60
    DIFF_ARG_TYPE = 61
    # Occurs if the TU the function lies in does not have a IFLAGS entry
    MISSING_COMPILE = 62
    # Triggered if a pointer field in a global struct has the same name
    # as a function
    NOT_RENAMED = 84
    # Array arguments are not supported for verification
    # (adding partial support should not be to compliated however)
    ARRAY_ARG = 85
    NONE = 255 # Base case used in `print_result`

@dataclass(init=True)
class IdentifierLocation:
    '''
    This class is equivalent to clang's SourceLocation
    except that it only contains simple properties
    and can thereby be hashed
    '''
    line: int
    column: int
    name: str

    # Always set to an _absolute path_
    _filepath: str

    @property
    def filepath(self) -> str:
        return self._filepath

    @filepath.setter
    def filepath(self,value):
        if not value.startswith("/"):
            print("!>", value)
            assert value.startswith("/")

        self._filepath = value

    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor, filepath:str="",
     name:str=""):
        '''
        During the impact stage we use the enclosing function name rather
        the cursor name (which corresponds to the function being called)
        '''
        # !! The file attribute must be converted to
        # a non-complex type to avoid mp deadlocks o.O
        obj = cls(
                _filepath = "",
                line = cursor.location.line,
                column = cursor.location.column,
                name = name if name != "" else cursor.spelling
        )
        obj.filepath = filepath if filepath != "" else str(cursor.location.file)
        return obj

    @classmethod
    def new_from_src_loc(cls, loc: cindex.SourceLocation,filepath:str=""):
        obj = cls(
            _filepath = "",
            line = loc.line,
            column = loc.column,
            name = ""
        )
        obj.filepath = filepath if filepath != "" else str(loc.file.name) # type: ignore
        return obj

    @classmethod
    def new_from_csv(cls, items:list[str]):
        return cls(
            _filepath=items[0],
            line=int(items[1]),
            column=int(items[2]),
            name=items[3]
        )

    @classmethod
    def empty(cls):
        return cls(_filepath = "", line = -1, column = -1, name = "")

    @classmethod
    def csv_header(cls, prefix:str="") -> str:
        prefix = f"{prefix}_" if prefix!="" else ""
        return f"{prefix}path;{prefix}line;{prefix}col;{prefix}name"

    def to_csv(self) -> str:
        return f"{self.filepath};{self.line};{self.column};{self.name}"

    def __hash__(self):
        return hash(str(self.line)+str(self.column)+str(self.filepath)+self.name)

@dataclass(init=True)
class Identifier:
    ''' 
    Refers to either a function argument or a function, 
    '''

    # The canonical type string for this identifier,
    # Note that double pointers will have a '*' in this
    # string as well as the is_ptr attribute set
    type_spelling: str

    # Derived from the string conversion of the clang type value
    # after 'TypeKind.' in lower case.
    # If the object refers to a function, the type reflects the return type
    typing: str

    location: IdentifierLocation = IdentifierLocation.empty()

    # Set for nodes that corresponds to function reference
    is_function: bool = False

    # If set, the identifier is a pointer to the specified type
    is_ptr: bool = False

    # If set, the identifier is defined with a const qualifier
    is_const: bool = False

    is_static: bool = False

    @classmethod
    def get_type_data(cls, clang_type: cindex.Type) -> tuple[bool,str,str]:
        '''
        To determine if a function is being called with the same types of 
        arguments as those specified in the prototype we need to resolve 
        all typedefs into their canonical representation. This infers that 
        the declarations created inside harnesses may look slightly different 
        from those in the original source code
        This should not be an issue though since the "parent" type resolves 
        in the same way.

        Some types are not properly resolved, for these we fallback to 
        the current value
        '''
        if re.search(CONFIG.UNRESOLVED_NODES_REGEX,
         clang_type.get_canonical().spelling):
            canonical = clang_type
        else:
            canonical = clang_type.get_canonical()

        # The is_const_qualified() attribute is not always reliable...
        is_const = canonical.is_const_qualified()
        #canonical.spelling.find("const ") != -1

        typing = str(canonical.kind).removeprefix("TypeKind.").lower()
        type_spelling = canonical.spelling.removeprefix("const ")

        # Ensure that the representation is the same regardless of white spaces
        type_spelling = re.sub(r" +", repl=" ", string = type_spelling)
        type_spelling = re.sub(r" \*", repl="*", string = type_spelling)

        return (is_const,typing,type_spelling)

    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor, filepath:str = ""):
        '''
        FUNCTIONPROTO is set for DECL_REF_EXPR and FUNCTION_DECL nodes,
        note that it is not set for 'CALL_EXPR' nodes
        '''
        is_decl = str(cursor.type.kind).endswith("FUNCTIONPROTO")
        is_call = str(cursor.kind).endswith("CALL_EXPR")

        # Dependent expressions e.g. the second argument in
        #   hashTableIterInit(&iter, &(p->elementTypes));
        # do not have a 'spelling' value,
        # In the situation above we can only resolve the type of 'p'...
        #
        # We have a dedicated check that excludes type checks for these types of
        # values
        if re.search(CONFIG.UNRESOLVED_NODES_REGEX, cursor.type.get_canonical().spelling):
            pass

        # For functions we are interested in the `.result_type`, this value
        # is empty for function arguments which instead 
        # have their typing in `.type`
        #
        # Note that this also applies for call expressions, these
        # have type values directly in cursor.type and not the result_type
        type_obj = cursor.result_type if is_decl else cursor.type

        result_pointee_type = type_obj.get_pointee()

        if result_pointee_type.spelling != "":
            # Pointer return type
            is_const, typing, type_spelling = cls.get_type_data(result_pointee_type)
            is_ptr = True
        else:
            is_const, typing, type_spelling = cls.get_type_data(type_obj)
            is_ptr = False

        if re.search(r"^int\**", type_spelling):
            type_spelling = cls.get_type_from_text(cursor, type_spelling,
                    filepath=filepath)

        return cls(
            typing = typing,
            type_spelling = type_spelling + ('*' if is_ptr else ''),
            is_ptr = is_ptr,
            is_const = is_const,
            is_function = (is_decl or is_call),
            is_static = str(cursor.storage_class).endswith("STATIC"),
            location = IdentifierLocation.new_from_cursor(cursor,
                filepath=filepath
            )
        )

    @classmethod
    def get_type_from_text(cls, cursor: cindex.Cursor, type_spelling: str,
            filepath:str="") -> str:
        '''
        ~~~ Hack ~~~
        Built-in typedefs like size_t do not get resolved properly
        and we resolve them by looking in the actual source file
        '''
        to_open = filepath if filepath != "" else str(cursor.location.file)
        try:
            with open(to_open, mode='r', encoding='utf8') as f:
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
        except IndexError:
            traceback.print_exc()
            print(f"!> Line out of range in {to_open}")


        return type_spelling

    @classmethod
    def empty(cls):
        return cls(
            typing="",
            type_spelling=""
        )

    def eq_report(self,other, return_value:bool, check_function:bool) -> str:
        '''
        When type-checking parameters against arguments we do not want to
        to check the function field since e.g. `foo( bar() )` is valid
        provided that the return value is correct (even though 
        it is a function unlike the param ident)
        '''
        same = "\033[32m✓\033[0m"
        differ = "\033[31mX\033[0m"

        if not check_function:
            # Ensure that the function param check cannot fail
            tmp = self.is_function
            self.is_function = other.is_function

        report = [
            f"type_spelling: {self.type_spelling} {other.type_spelling} " + \
                    (same if self.type_spelling == other.type_spelling else differ),
            f"(strict) typing: {self.typing} {other.typing} " + \
                    (same if self.typing == other.typing else differ),
            f"(strict) is_ptr: {self.is_ptr} {other.is_ptr}: " + \
                    (same if self.is_ptr == other.is_ptr else differ),
            f"(strict) is_const: {self.is_const} {other.is_const} " + \
                    (same if self.is_const == other.is_const else differ),
            f"(strict) is_static: {self.is_static} {other.is_static} " + \
                    (same if self.is_static == other.is_static else differ),
            f"is_function: {self.is_function} {other.is_function} " + \
                    (same if self.is_function == other.is_function else differ)
        ]

        if self != other:
            ret = \
                "Incompatible types " + \
                ("(return value)" if return_value else "(parameter)") + \
                f" '{self.location.name}' - '{other.location.name}'\n  " + '\n  '.join(report)
        else:
            ret = ""

        if not check_function:
            self.is_function = tmp # type: ignore

        return ret

    def __eq__(self, other) -> bool:
        ''' 
        Does not consider nodes which only differ in spelling or location
        as different. Function calls and function decls are also considered the same

        Unresolved nodes with a 'dependent type' are considered equal to everything
        unless we are using STRICT_TYPECHECKS
        We only check the function_flag and type_spelling if STRICT_TYPECHECKS is not set,
        Type checking through python's clang bindings is very FP prone
        '''
        strict_check = True
        if CONFIG.STRICT_TYPECHECKS:
            strict_check = self.typing == other.typing and \
               self.is_ptr == other.is_ptr and \
               self.is_const == other.is_const and \
               self.is_static == other.is_static

        elif re.search(CONFIG.UNRESOLVED_NODES_REGEX, self.type_spelling) or \
           re.search(CONFIG.UNRESOLVED_NODES_REGEX, other.type_spelling):
            return True

        # The type spelling usually differs slightly between declarations and
        # call sites, e.g. the call site usually does not have an 'enum' prefix
        # for enums
        return strict_check and \
               self.type_spelling.removeprefix("enum ") == \
               other.type_spelling.removeprefix("enum ") and \
               self.is_function == other.is_function

    def __repr__(self, paranthesis: bool = True, use_suffix:bool=False):
        constant = 'const ' if self.is_const else ''
        func = '()' if self.is_function and paranthesis else ''

        # Types that should be explicitly renamed will be given a suffix
        # with their type string and spelling if the use_suffix flag is set
        #
        base_type = self.type_spelling.removeprefix("struct") \
            .strip(' *')

        if use_suffix and base_type in CONFIG.EXPLICIT_RENAME:
            struct = "struct " if self.type_spelling.startswith("struct") else ''
            type_str = f"{struct}{base_type}{CONFIG.SUFFIX}"

            if self.type_spelling.endswith("*"):
                type_str = f"{type_str}*"

            spelling_str = self.location.name+CONFIG.SUFFIX
        else:
            type_str = self.type_spelling
            spelling_str = self.location.name

        # Arrays will have '[]' within their type string (rather than
        # the symbol name)
        if (bracket_idx := type_str.strip().find("[]")) >= 0:
            type_str = type_str.strip()[0:bracket_idx]
            spelling_str += "[]"

        return f"{constant}{type_str} {spelling_str}{func}"

    def dump(self, header:bool = False) -> str:
        fmt =  "is_const;is_ptr;is_function;typing;type_spelling;spelling\n" \
                if header else ''
        fmt += \
        f"{self.is_const};{self.is_ptr};{self.is_function};{self.typing};"+\
        f"{self.type_spelling};{self.location.name}"
        return fmt

@dataclass(init=True)
class DependencyFunction:
    ''' 
    A function which is transitively changed due to invoking either
    a directly changed function or another transitively changed function
    will have the `invokes_changed_function` attribute set to a non-empty list 

    We pair functions based on the key:
    {diff.filepath_new}:{diff.filepath_old}:{child.spelling}
    All other attributes could thus differ between the new and old version.
    '''
    displayname: str # Includes the full prototype string
    ident: Identifier # Function name and return type
    # The arguments must be in correct order within the list
    arguments: list[Identifier]

    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor, filepath: str = ""):
        return cls(
            displayname = cursor.displayname,
            ident        = Identifier.new_from_cursor(cursor, filepath=filepath),
            arguments   = [ Identifier.new_from_cursor(arg, filepath=filepath)
                  for arg in cursor.get_arguments() ],
        )

    @classmethod
    def empty(cls):
        return cls(
            displayname = "",
            ident       = Identifier.empty(),
            arguments   = [],
        )

    def prototype_string(self, suffix: str = "") -> str:
        out = f"{self.ident.__repr__(paranthesis=False)}{suffix}("
        for arg in self.arguments:
            if suffix != "":
                out += f"{arg.__repr__(use_suffix=True)}, "
            else:
                out += f"{arg}, "

        return out.removesuffix(", ") + ")"

    def __hash__(self):
        return hash(self.ident.location.to_csv() + self.displayname)

@dataclass(init=True)
class DependencyFunctionChange:
    old: DependencyFunction
    new: DependencyFunction

    # NOTE: We need to use a set() since if a header defines a 
    # function, several TUs may parse the function multiple times, 
    # causing duplicate entries to be added if the function calls a 
    # function in the change set. This is not an issue for regular .c files
    invokes_changed_functions: set[str]
    direct_change: bool = True

    # The source code location (in the old version)
    # were divergence in the AST was encountered
    # This will be unset for indirect changes in the transitive pass
    point_of_divergence: IdentifierLocation = IdentifierLocation.empty()

    @classmethod
    def new_from_cursors(cls, cursor_old: cindex.Cursor, cursor_new:
     cindex.Cursor, filepath_old:str="", filepath_new:str=""):
        return cls(
            old = \
            DependencyFunction.new_from_cursor(cursor_old,filepath=filepath_old),
            new = \
            DependencyFunction.new_from_cursor(cursor_new,filepath=filepath_new),
            invokes_changed_functions = set()
        )

    @classmethod
    def new_from_change_set_csv(cls, items:list[str]):
        assert len(items) == 9
        old = DependencyFunction.empty()
        old.ident.location = IdentifierLocation.new_from_csv(items[1:5])
        new = DependencyFunction.empty()
        new.ident.location = IdentifierLocation.new_from_csv(items[5:9])
        return cls(
                direct_change = items[0] == "True",
                old = old, new = new,
                invokes_changed_functions = set(),
        )

    @classmethod
    def csv_header(cls) -> str:
        return f"direct_change;{IdentifierLocation.csv_header('old')};"+\
               f"{IdentifierLocation.csv_header('new')}"

    def to_csv(self) -> str:
        return f"{self.direct_change};{self.old.ident.location.to_csv()};"+\
               f"{self.new.ident.location.to_csv()}"

    def __hash__(self):
        ''' 
        Note that the hash does not consider the `invokes_changed_functions` 
        list. A set will thus only include one copy of each function
        '''
        return hash(self.old.ident.location.to_csv() + \
               self.new.ident.location.to_csv())

@dataclass(init=True)
class CallSite:
    called_function_change: DependencyFunctionChange
    call_location: IdentifierLocation

    @classmethod
    def csv_header(cls) -> str:
        return f"{IdentifierLocation.csv_header('impacted')};"+\
                DependencyFunctionChange.csv_header()

    def to_csv(self):
        return f"{self.call_location.to_csv()};" + \
               f"{self.called_function_change.to_csv()}"

@dataclass(init=True)
class SourceFile:
    '''
    Includes helper functions for creating the compile arguments
    needed by libclang
    '''

    # _Absolute path_ to the new version of the file
    _filepath_new: str

    compile_args_new: list[str] = field(default_factory=list)
    compile_dir_new: str = ""

    @property
    def filepath_new(self) -> str:
        return self._filepath_new

    @filepath_new.setter
    def filepath_new(self,value):
        assert value.startswith("/")
        self._filepath_new = value

    @classmethod
    def get_isystem_flags(cls, source_file: str, compile_dir: str) -> list:
        '''
        (This should not really be a class function)
        https://clang.llvm.org/docs/FAQ.html#id2
        The -cc1 flag is used to invoke the clang 'frontend', using only the
        frontend infers that default options are lost, errors like
            'stddef.h' file not found
        are caused from the fact that the builtin-include path of 
        clang is missing. We can see the default frontend options 
        used by clang with
            clang -### test/file.cpp
        Output format (stderr):

        1 <version>
        2 <target>
        3 <thread model>
        4 <installed_dir>
        5 <default frontend arguments>: "/usr/lib/llvm-13/bin/clang" "-cc1"
        "-triple" "x86_64-pc-linux-gnu" "-emit-obj" "-mrelax-all"
        "--mrelax-relocations" ...
        6 <default linker arguments>: "/usr/bin/ld" "-z" "relro" 
        "--hash-style=gnu" "--build-id" "--eh-frame-hdr" ...
        '''
        out = []
        with subprocess.Popen(f"{CONFIG.CCDB_CC} -### {source_file}",
            shell=True, cwd = compile_dir, stderr=subprocess.PIPE
            ) as p:
            output = p.stderr.read().decode('utf8').splitlines() # type: ignore
            assert len(output) == 6

            items =  [ s.strip("\"") for s in output[4].split() ]

            use_next = False
            for item in items:
                if item == "-internal-isystem":
                    out.append(item)
                    use_next = True
                elif use_next:
                    # Do not include missing paths
                    if os.path.isdir(item):
                        out.append(item)
                    else:
                        out.pop()
                    use_next = False
        return out

    @classmethod
    def get_compile_args(cls, compile_db: cindex.CompilationDatabase,
         filepath: str, isystem_flags: list[str]|None = None) -> \
    tuple[str,list[str]]:
        ''' 
        Load the compilation configuration for the particular file
        and retrieve the compilation arguments and the directory that
        the file should be compiled in 
        '''
        ccmds: cindex.CompileCommands = compile_db.getCompileCommands(filepath)
        if ccmds:
            compile_args = list(ccmds[0].arguments)
            compile_dir  = str(ccmds[0].directory)

            # We need each isystem flag to be passed to clang directly
            # and therefore prefix every argument with -Xclang
            if isystem_flags is None:
                isystem_flags = cls.get_isystem_flags(filepath,compile_dir)
            xclang_flags = []
            for flag in isystem_flags:
                xclang_flags.append("-Xclang")
                xclang_flags.append(flag)

            # Remove the first (/usr/bin/cc) and last (source_file) 
            # arguments from the command list
            flags = xclang_flags + compile_args[1:-1]

            # Strip away warnings
            flags = list(filter(lambda f: not f.startswith("-W"), flags))

            # Add custom flags
            flags += CONFIG.EXTRA_COMPILE_FLAGS

            return (compile_dir, flags)

        raise Exception(f"No compilation instructions for {filepath}")

    @classmethod
    def new(cls, filepath: str, ccdb: cindex.CompilationDatabase):
        (compile_dir_new, compile_args_new) = \
                cls.get_compile_args(ccdb, filepath)
        obj = cls(
            _filepath_new = "/",
            compile_dir_new = compile_dir_new,
            compile_args_new = compile_args_new
        )
        obj.filepath_new = filepath
        return obj

    def __repr__(self) -> str:
        return f"{self.filepath_new} [" + ' '.join(self.compile_args_new) + "]"

@dataclass(init=True)
class SourceDiff(SourceFile):
    compile_args_old: list[str] = field(default_factory=list)
    compile_dir_old: str = ""

    # _Absolute path_ to the old version of the file
    _filepath_old: str = ""

    @property
    def filepath_old(self) -> str:
        return self._filepath_old

    @filepath_old.setter
    def filepath_old(self,value):
        assert value.startswith("/")
        self._filepath_old = value

    @classmethod
    def new(cls, filepath_old: str, ccdb_old: cindex.CompilationDatabase,
      filepath_new: str, ccdb_new: cindex.CompilationDatabase):
        '''
        Create a new object using the super() class constructor
        '''
        (compile_dir_old, compile_args_old) = \
          cls.get_compile_args(ccdb_old, filepath_old)

        s = super().new(filepath_new, ccdb_new)

        obj = cls(
            _filepath_old = "/", compile_args_old = compile_args_old,
            compile_dir_old = compile_dir_old,
            _filepath_new = "/", compile_args_new = s.compile_args_new,
            compile_dir_new = s.compile_dir_new
        )
        obj.filepath_old = filepath_old
        obj.filepath_new = filepath_new
        return obj

@dataclass(init=True)
class CursorPair:
    new: cindex.Cursor
    old: cindex.Cursor
    filepath_new: str
    filepath_old: str

    def __init__(self):
        self.new = None # type: ignore
        self.old = None # type: ignore

@dataclass(init=True)
class SubDirTU:
    files: set[str] = field(default_factory=set)
    ccdb_args: set[str] = field(default_factory=set)

    def add_from_tu(self, tu: dict):
        ''' 
        The TU argument corresponds to one entry from a compile_commands.json
        Note the use of [1:-3] to skip over the cc and output files
        '''
        self.files.add(tu['file'])
        self.ccdb_args |= set(tu['arguments'][1:-3])

@dataclass(init=True)
class StateParam:
    name: str = ""
    nondet: bool = False # Must be explicitly set
    states: set = field(default_factory=set)

@dataclass(init=True)
class FunctionState:
    ''' 
    The value for a parameter will be '[]' or False if its nondet 
    Each item in the parameters array is on the form
        [0]:    { <param name>, <states>,  <det> }
    We use a list rather than a dict since the argument order is important

    The actual function name will be the key of dict mapped to this object
    '''
    parameters: list[StateParam] = field(default_factory=list)

    def add_state_values(self, param_name:str, idx: int, values: set) -> None:
        '''
        The parameter will be an integer if the declaration has it unnamed
        '''

        # Add entries to ensure that we can insert the current param
        # at the correct index
        while len(self.parameters) <= idx:
            self.parameters.append(StateParam()) # defaults to nondet() 

        # Skip setting the name if its a placeholder set by the clang plugin
        if not param_name.isnumeric():
            self.parameters[idx].name = param_name

        if len(values) == 0: # nondet() parameter
            self.parameters[idx].nondet = True
        elif not self.parameters[idx].nondet:
            # det() parameter: join the current set of states with those
            # provided in 'values'
            self.parameters[idx].states |= values

@dataclass(init=True)
class Cstruct:
    name: str
    fields: set[str] = field(default_factory=set)

    def __hash__(self):
        return hash(self.name + ''.join(list(self.fields)))
