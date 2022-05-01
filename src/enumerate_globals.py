import os, traceback
from pprint import pprint
from clang import cindex
from src import BASE_DIR

from src.util import flatten, has_allowed_suffix, print_warn, \
  time_start, time_end, print_err
from src.config import CONFIG
from src.types import Cstruct, Identifier, SourceFile

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_top_level_decls(cursor: cindex.Cursor, compile_dir: str ) \
-> list[Identifier]:
    ''' 
    Extract the names of all top level declarations that should be renamed:
        - Non static global variables
        - All functions (we want to be able to verify static functions)
    excluding those defined externally under /usr/include

    We include if the symbol is static or not, this becomes relevant if
    there are overlaps between fields in global structs and the symbol name
    '''
    global_decls = []

    for child in cursor.get_children():

        is_function_decl  = str(child.kind).endswith("FUNCTION_DECL") and \
          child.is_definition()
        is_var_decl = str(child.kind).endswith("VAR_DECL") and \
           not str(child.storage_class).endswith("STATIC")

        location_str = str(child.location.file)

        if (is_function_decl or is_var_decl) and \
          not location_str.startswith("/usr/include"):

            if not location_str.startswith("/"):
                # If a file location is not given as an absolute path
                # we prepend the directory of the current cursor
                location_str = f"{compile_dir}/{location_str}"

            global_decls.append(
                    Identifier.new_from_cursor(child,location_str)
            )

    return global_decls

def get_top_level_structs(cursor: cindex.Cursor) -> set[Cstruct]:
    '''
    Enumerate the names of all function pointer fields in struct at the top
    level in a file. If any of these fields intersect with actual function names
    we need to exclude them from renaming since the structs would be incorrectly
    modified during the renaming stage.

    It is OK for a global variable to intersect with a struct field
    since CBMC does not try to resolve these in the same way as function
    pointers.
    '''
    structs: set[Cstruct] = set()

    for child in cursor.get_children():
        if str(child.kind).endswith("STRUCT_DECL"):
            struct = Cstruct(child.spelling)
            for field in child.get_children():
                if str(field.kind).endswith("FIELD_DECL") and \
                   str(field.type.get_pointee().kind).endswith("FUNCTIONPROTO"):
                    struct.fields.add(field.spelling)
            structs.add(struct)

    return structs;

def get_global_identifiers(source_dir: str, ccdb: cindex.CompilationDatabase) \
 -> tuple[list[Identifier],set[str]]:
    '''
    Creates a set of all top level symbols (as Identifier objects) in the
    dependency. Each of these need to be given a suffix to avoid conflicts
    Note: We iterate over the files in the ccdb and NOT the our array
    of SourceFile objects since this array can be pruned from certain files
    based on the EXCLUDE_REGEXES option
    '''
    os.chdir(source_dir)

    global_identifiers: list[Identifier] = []
    structs: set[Cstruct] = set()
    filepaths: set[str] = set()

    start_time = time_start(f"Enumerating global symbols...")
    try:
        for ccmds in ccdb.getAllCompileCommands():
            # Depending on how the compile_commands.json is read
            # the full path may or may not be present...
            filepath = ccmds.filename

            # Skip files in other formats, e.g. asm
            if not has_allowed_suffix(filepath):
                continue

            if not filepath.startswith(source_dir):
                filepath = f"{source_dir}/{filepath.lstrip('/')}"

            filepaths.add(filepath)

            try:
                compile_dir,compile_args = \
                    SourceFile.get_compile_args(ccdb,filepath,source_dir)

                os.chdir(compile_dir)
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = compile_args
                )
                cursor: cindex.Cursor = tu.cursor
                global_identifiers.extend(
                        get_top_level_decls(cursor, compile_dir)
                )
                structs |= get_top_level_structs(cursor)

            except cindex.TranslationUnitLoadError:
                if CONFIG.VERBOSITY >= 4:
                    print(traceback.format_exc())
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {source_dir}/compile_commands.json")

    idents, skip_renaming = handle_struct_conflicts(structs, global_identifiers)

    time_end("Global symbol enumeration", start_time)
    os.chdir(BASE_DIR)

    return idents, skip_renaming

def handle_struct_conflicts(structs: set[Cstruct],
 idents: list[Identifier]) -> tuple[list[Identifier],set[str]]:
    '''
    Remove all functions which are statically defined 
    and have a name that overlaps with a struct field from the idents set.
    We keep non-static functions with an overlap in the set and show
    a warning regarding this
    '''
    field_names = set(flatten([ list(s.fields) for s in structs ]))

    non_static_functions = filter(lambda f: not f.is_static and f.is_function, idents)
    non_static_function_names = set([ f.location.name for f in non_static_functions ]);

    static_functions = filter(lambda f: f.is_static and f.is_function, idents)
    static_function_names = set([ f.location.name for f in static_functions ]);

    static_overlap = field_names & static_function_names

    if len(static_overlap) > 0 and CONFIG.VERBOSITY >= 1:
        print_warn("The following static functions overlap with fields in " +
            "globally defined structs and will be excluded from CBMC analysis:"
        )
        print(static_overlap, flush=True)

    illegal_overlap = field_names & non_static_function_names

    if len(illegal_overlap) > 0 and CONFIG.VERBOSITY >= 1:
        print_warn("The following functions are non-static " +
                "and cannot be excluded from renaming. " +
                "This may cause errors. Adding the struct(s) " +
                "with overlapping field names to " +
                "EXPLICIT_RENAME may partially solve this.")
        for struct in structs:
            if len(illegal_overlap & struct.fields) > 0:
                pprint(struct)
        print(illegal_overlap, flush=True)

    # Return all symbols except for functions that are statically
    # defined AND overlap with a field name
    not_in_static_overlap = list(filter(lambda i:
        not i.location.name in static_overlap, idents
    ))

    return not_in_static_overlap, static_overlap

def read_in_names(rename_txt: str, names: set[str]):
    with open(rename_txt, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            names.add(line.rstrip("\n"))

def write_rename_files(global_identifiers: list[Identifier]):
    ''' 
    Dump a list of global_name;line;col names to disk 
    along with a newline separated file containing just the global names 
    '''
    ident_locations = set([ g.location for g in global_identifiers ])

    # Only produced for debugging purposes
    with open(CONFIG.RENAME_CSV, "w", encoding="utf8") as f:
        f.write("filepath;name;line;column\n")
        for location in ident_locations:
            f.write(f"{location.to_csv()}\n")

        for name in CONFIG.EXPLICIT_RENAME:
            f.write(f";{name};;\n")

    # Used by CBMC when invoked with 'USE_SUFFIX'
    # In this version we strip out any duplicate occurrences of the same name
    global_names = set([ g.location.name for g in global_identifiers ])

    with open(CONFIG.RENAME_TXT, "w", encoding="utf8") as f:
        for name in global_names:
            f.write(f"{name}\n")
        for name in CONFIG.EXPLICIT_RENAME:
            f.write(f"{name}\n")
