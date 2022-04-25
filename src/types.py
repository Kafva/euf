import re, subprocess
from dataclasses import dataclass, field
from enum import Enum

from clang import cindex
from src.config import CONFIG

class AnalysisResult(Enum):
    SUCCESS = 0 # SUCCESS verification: equivalent change
    ERROR = 1
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
    NONE = 255 # Basecase used in `print_result`

@dataclass(init=True)
class Identifier:
    ''' 
    Refers to either a function argument or a function, 
    '''

    spelling: str

    # The canoncial type string for this identifier,
    # Note that double pointers will have a '*' in this
    # string as well as the is_ptr attribute set
    type_spelling: str

    # Derived from the string conversion of the clang type value
    # after 'TypeKind.' in lower case.
    # If the object refers to a function, the type reflects the return type
    typing: str

    # Set for nodes that corresponds to function reference
    is_function: bool = False

    # If set, the identifier is a pointer to the specified type
    is_ptr: bool = False

    # If set, the identifier is defined with a const qualifer
    is_const: bool = False


    @classmethod
    def get_type_data(cls, clang_type: cindex.Type) -> tuple[bool,str,str]:
        '''
        To determine if a function is being called with the same types of arguments
        as those specified in the prototype we need to resolve all typedefs into
        their canoncial representation. This infers that the declarations created
        inside harnesses may look slightly different from those in the original source code
        This should not be an issue though since the "parent" type resolves in the same way

        Some types are not properly resolved, for these we fallback to the current value
        '''
        if re.search(CONFIG.UNRESOLVED_NODES_REGEX, clang_type.get_canonical().spelling):
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
    def get_underlying_args(cls,cursor: cindex.Cursor, level:int):
        for child in cursor.get_arguments():
            print("  "*level, child.type.kind, child.kind, child.spelling,
                    child.type.get_pointee().spelling,
                    child.type.get_pointee().kind,
            )
            cls.get_underlying_args(child, level+1)

        return cursor

    @classmethod
    def get_underlying_node(cls,cursor: cindex.Cursor, level:int):
        for child in cursor.get_children():
            print("  "*level, child.type.kind, child.kind, child.spelling,
                    child.type.get_pointee().spelling,
                    child.type.get_pointee().kind,
            )
            cls.get_underlying_args(child, level)
            cls.get_underlying_node(child, level+1)

        return cursor

    @classmethod
    def new_from_cursor(cls, cursor: cindex.Cursor):
        '''
        FUNCTIONPROTO is set for DECL_REF_EXPR and FUNCTION_DECL nodes,
        note that it is not set for 'CALL_EXPR' nodes
        '''
        is_decl = str(cursor.type.kind).endswith("FUNCTIONPROTO")
        is_call = str(cursor.kind).endswith("CALL_EXPR")

        # Dependent experssions e.g. the second argument in
        #   hashTableIterInit(&iter, &(p->elementTypes));
        # do not have a 'spelling' value,
        # In the situation above we can only resolve the type of 'p'...
        #
        # We have a dedicated check that excludes type checks for these types of
        # values
        if re.search(CONFIG.UNRESOLVED_NODES_REGEX, cursor.type.get_canonical().spelling):
            #cls.get_underlying_node(cursor,1)
            #cls.get_underlying_args(cursor,1)
            pass

        # For functions we are intrested in the `.result_type`, this value
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
            type_spelling = cls.get_type_from_text(cursor, type_spelling)

        return cls(
            spelling = cursor.spelling,
            typing = typing,
            type_spelling = type_spelling + ('*' if is_ptr else ''),
            is_ptr = is_ptr,
            is_const = is_const,
            is_function = (is_decl or is_call)
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

    def eq_report(self,other, return_value:bool, check_function:bool) -> str:
        '''
        When type-checking paramters against arguments we do not want to
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
            f"is_function: {self.is_function} {other.is_function} " + \
                    (same if self.is_function == other.is_function else differ)
        ]

        if self != other:
            ret = \
                "Incompatible types " + \
                ("(return value)" if return_value else "(parameter)") + \
                f" '{self.spelling}' - '{other.spelling}'\n  " + '\n  '.join(report)
        else:
            ret = ""

        if not check_function:
            self.is_function = tmp # type: ignore

        return ret

    def __eq__(self, other) -> bool:
        ''' 
        Does not consider nodes which only differ in spelling
        as different. Function calls and function decls are also considered the same

        Unresolved nodes with a 'dependent type' are considered equal to everything
        unless we are using STRICT_TYPECHECKS
        We only check the function_flag and type_spelling if STRICT_TYPECHECKS is not set,
        Typechecking through python's clang bindings is very FP prone
        '''
        strict_check = True
        if CONFIG.STRICT_TYPECHECKS:
            strict_check = self.typing == other.typing and \
               self.is_ptr == other.is_ptr and \
               self.is_const == other.is_const

        elif re.search(CONFIG.UNRESOLVED_NODES_REGEX, self.type_spelling) or \
             re.search(CONFIG.UNRESOLVED_NODES_REGEX, other.type_spelling):
                return True

        # The type spelling usuaully differs slightly between declerations and
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
        base_type = self.type_spelling.removeprefix("struct").strip(' *')

        if use_suffix and base_type in CONFIG.EXPLICIT_RENAME:
            struct = "struct " if self.type_spelling.startswith("struct") else ''
            type_str = f"{struct}{base_type}{CONFIG.SUFFIX}"

            if self.type_spelling.endswith("*"):
                type_str = f"{type_str}*"

            spelling_str = self.spelling+CONFIG.SUFFIX
        else:
            type_str = self.type_spelling
            spelling_str = self.spelling

        return f"{constant}{type_str} {spelling_str}{func}"

    def dump(self, header:bool = False) -> str:
        fmt =  "is_const;is_ptr;is_function;typing;type_spelling;spelling\n" if header else ''
        fmt += f"{self.is_const};{self.is_ptr};{self.is_function};{self.typing};{self.type_spelling};{self.spelling}"
        return fmt

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
                # !! The file attribute must be converted to
                # a non-complex type to avoid mp deadlocks o.O
                filepath = str(cursor.location.file),
                name = cursor.spelling
        )

    @classmethod
    def new_from_src_loc(cls, loc: cindex.SourceLocation):
        return cls(
            filepath = str(loc.file.name), # type: ignore
            line = loc.line,
            column = loc.column,
            name = ""
        )

    @classmethod
    def empty(cls):
        return cls(filepath = "", line = -1, column = -1, name = "")

    @classmethod
    def csv_header(cls, prefix:str="") -> str:
        prefix = f"{prefix}_" if prefix!="" else ""
        return f"{prefix}path;{prefix}line;{prefix}col;{prefix}name"

    def __repr__(self) -> str:
        if self.name != "":
            return f"{self.filepath}:{self.line}:{self.column}:{self.name}"
        else:
            return f"{self.filepath}:{self.line}:{self.column}"


    def to_csv(self) -> str:
        return f"{self.filepath};{self.line};{self.column};{self.name}"

    def __hash__(self):
        return hash(str(self.line)+str(self.column)+str(self.filepath)+self.name)

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
    ident: Identifier # Function name and return type
    location: IdentifierLocation
    arguments: list[Identifier] # The arguments must be in correct order within the list
    is_static: bool = False

    @classmethod
    def new_from_cursor(cls, root_dir: str, cursor: cindex.Cursor):
        filepath = str(cursor.location.file).removeprefix(root_dir).removeprefix("/")
        return cls(
            location = IdentifierLocation(
                filepath=filepath,
                line=cursor.location.line,
                column=cursor.location.column,
                name = cursor.spelling
            ),
            displayname = cursor.displayname,
            ident        = Identifier.new_from_cursor(cursor),
            arguments   = [ Identifier.new_from_cursor(arg)
                  for arg in cursor.get_arguments() ],
            is_static = str(cursor.storage_class).endswith("STATIC")
        )

    @classmethod
    def empty(cls):
        return cls(
            displayname = "",
            ident       = Identifier.empty(),
            arguments   = [],
            location = IdentifierLocation.empty(),
        )

    def eq(self, other) -> bool:
        '''
        Ensure that the arguments and return value of the provided function
        match that of the current function object. Does not check the filepath
        '''
        if (err := self.ident.eq_report(other.ident, return_value=True, check_function=True)) != "":
            print(err)
            print(f"definition: {self}\ncall: {other}\n")
            return False

        for self_arg,other_arg in zip(self.arguments,other.arguments):
            if (err := self_arg.eq_report(other_arg, return_value=False, check_function=False)) != "":
                print(err)
                print(f"definition: {self}\ncall: {other}\n")
                return False

        return True

    def __repr__(self):
        return f"{self.location}()"

    def prototype_string(self, suffix: str = "") -> str:
        out = f"{self.ident.__repr__(paranthesis=False)}{suffix}("
        for arg in self.arguments:
            if suffix != "":
                out += f"{arg.__repr__(use_suffix=True)}, "
            else:
                out += f"{arg}, "

        return out.removesuffix(", ") + ")"

    def __hash__(self):
        return hash(self.location.__repr__() + self.ident.__repr__() + self.displayname)

@dataclass(init=True)
class DependencyFunctionChange:
    old: DependencyFunction
    new: DependencyFunction

    invokes_changed_functions: list[str]
    direct_change: bool = True

    # The source code location (in the old version)
    # were divergence in the AST was encountered
    # This will be unset for indirect changes in the transative pass
    point_of_divergence: IdentifierLocation = IdentifierLocation.empty()

    @classmethod
    def new_from_cursors(cls, old_root: str, new_root: str,
            old_cursor: cindex.Cursor, new_cursor: cindex.Cursor):
        return cls(
            old = DependencyFunction.new_from_cursor(old_root, old_cursor),
            new = DependencyFunction.new_from_cursor(new_root, new_cursor),
            invokes_changed_functions = []
        )

    @classmethod
    def csv_header(cls) -> str:
        return f"direct_change;{IdentifierLocation.csv_header('old')};{IdentifierLocation.csv_header('new')}"

    def divergence(self,with_context:bool=True) -> str:
        if with_context:
            return f"{self.__repr__()}\n{CONFIG.INDENT}diverged at \033[4m{self.point_of_divergence}\033[0m"
        else:
            return f"\n{CONFIG.INDENT}diverged at \033[4m{self.point_of_divergence}\033[0m"

    def affected_by(self,pretty=True) -> str:
        out = ""
        if len(self.invokes_changed_functions) > 0:
            if pretty:
                out += "\nAffected by changes to:"
            else:
                out += "\n affected by changes to:"

            for trans_call in self.invokes_changed_functions:
                out += f"\n{CONFIG.INDENT}{trans_call}"
        return out

    def to_csv(self) -> str:
        return f"{self.direct_change};{self.old.location.to_csv()};{self.new.location.to_csv()}"

    def __repr__(self, pretty: bool = False, brief: bool = False):
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

        if not brief:
            out += self.affected_by(pretty)

        return out

    def __hash__(self):
        ''' 
        Note that the hash does not consider the `invokes_changed_functions` 
        list. A set will thus only include one copy of each function
        '''
        return hash(hash(self.old) + hash(self.new))

@dataclass(init=True)
class CallSite:
    called_function_change: DependencyFunctionChange
    call_location: IdentifierLocation

    @classmethod
    def csv_header(cls) -> str:
        return f"{IdentifierLocation.csv_header('impacted')};{DependencyFunctionChange.csv_header()}"

    def to_csv(self):
        return f"{self.call_location.to_csv()};" + \
               f"{self.called_function_change.to_csv()}"

    def __repr__(self):
        return f"call to {self.called_function_change.new} at {self.call_location}()"

@dataclass(init=True)
class SourceFile:
    '''
    Includes helper functions for creating the compile arguments
    needed by libclang
    '''
    new_path: str
    new_compile_args: list[str] = field(default_factory=list)
    new_compile_dir: str = ""

    @classmethod
    def get_isystem_flags(cls, source_file: str, dep_path: str) -> list:
        '''
        (This should not really be a class function)
        https://clang.llvm.org/docs/FAQ.html#id2
        The -cc1 flag is used to invoke the clang 'frontend', using only the
        frontend infers that default options are lost, errors like
            'stddef.h' file not found
        are caused from the fact that the builtin-include path of clang is missing
        We can see the default frontend options used by clang with
            clang -### test/file.cpp
        '''
        isystem_flags = subprocess.check_output(
            f"clang -### {source_file} 2>&1 | sed -E '1,4d; s/\" \"/\", \"/g; s/(.*)(\\(in-process\\))(.*)/\\1\\3/'",
            shell=True, cwd = dep_path
        ).decode('ascii').split(",")

        out = []
        add_next = False

        for flag in isystem_flags:
            flag = flag.strip().strip('"')

            if flag == '-internal-isystem':
                out.append(flag)
                add_next = True
            elif add_next:
                out.append(flag)
                add_next = False

        return out

    @classmethod
    def get_compile_args(cls, compile_db: cindex.CompilationDatabase,
        filepath: str, repo_path: str) -> tuple[str,list[str]]:
        ''' 
        Load the compilation configuration for the particular file
        and retrieve the compilation arguments and the directory that
        the file should be compiled in 
        '''
        ccmds: cindex.CompileCommands   = compile_db.getCompileCommands(filepath)
        if ccmds:
            compile_args                    = list(ccmds[0].arguments)
            compile_dir                     = str(ccmds[0].directory)

            # We need each isystem flag to be passed to clang directly
            # and therefore prefix every argument with -Xclang
            isystem_flags = cls.get_isystem_flags(filepath,repo_path)
            xclang_flags = []
            for flag in isystem_flags:
                xclang_flags.append("-Xclang")
                xclang_flags.append(flag)

            # Remove the first (/usr/bin/cc) and last (source_file) arguments from the command list
            flags = xclang_flags + compile_args[1:-1] + CONFIG.EXTRA_COMPILE_FLAGS

            # Strip away warnings
            flags = list(filter(lambda f: not f.startswith("-W"), flags))

            return (compile_dir, flags)
        else:
            raise Exception(f"Failed to retrieve compilation instructions for {filepath}")

    @classmethod
    def new(cls, filepath: str, ccdb: cindex.CompilationDatabase, dep_path: str):
        (new_compile_dir, new_compile_args) = \
                cls.get_compile_args(ccdb, filepath, dep_path)
        return cls(
            new_path = filepath,
            new_compile_dir = new_compile_dir,
            new_compile_args = new_compile_args
        )

@dataclass(init=True)
class SourceDiff(SourceFile):
    old_path: str = ""
    old_compile_args: list[str] = field(default_factory=list)
    old_compile_dir: str = ""

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
        The parameter will be an integer if the declaration has it unamed
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

