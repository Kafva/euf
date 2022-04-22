import os, traceback
from clang import cindex

from cparser.util import has_allowed_suffix, time_start, time_end, print_err
from cparser.config import CONFIG
from cparser.types import IdentifierLocation

def dump_children(cursor: cindex.Cursor, indent: int) -> None:
    for child in cursor.get_children():
        if child.spelling != "":
            print(indent * " ", end='')
            print(f"{child.kind} {child.type.kind} {child.spelling}")
            indent += 1
        dump_children(child, indent)

def get_top_level_decl_locations(cursor: cindex.Cursor) -> set[IdentifierLocation]:
    ''' 
    Extract the names of all top level declerations (variables and functions) 
    excluding those defined externally under /usr/include
    '''
    global_decls: set[IdentifierLocation] = set()

    for child in cursor.get_children():
        if  str(child.kind).endswith("FUNCTION_DECL") and \
            child.is_definition() and \
            not str(child.location.file).startswith("/usr/include"):
        #if (str(child.kind).endswith("FUNCTION_DECL") or \
        #    str(child.kind).endswith("VAR_DECL")) and \
        #    child.is_definition() and \
        #    not str(child.location.file).startswith("/usr/include"):
                global_decls.add(
                        IdentifierLocation.new_from_cursor(child)
                )

    return global_decls

def get_global_identifiers(basepath: str, ccdb: cindex.CompilationDatabase) -> set[IdentifierLocation]:
    '''
    Reads the compilation database and creates:
        A set of all top level labels in the changed files that we need to
        rename with a suffix as IdentifierLocation objects:
        filepath;global_name;line;col
    Note that the filepath refers to the file were the symbol was found,
    it can very well exist in more TUs
    '''
    os.chdir(basepath)

    start_time = time_start(f"Enumerating global symbols...")

    global_identifiers: set[IdentifierLocation] = set()
    filepaths: set[str] = set()

    try:
        for ccmds in ccdb.getAllCompileCommands():
            # Depending on how the compile_commands.json is read
            # the full path may or may not be present...
            filepath = ccmds.filename

            # Skip files in other formats, e.g. asm
            if not has_allowed_suffix(filepath):
                continue

            if not filepath.startswith(basepath):
                filepath = basepath + "/" + filepath

            if filepath in filepaths:
                continue # Skip duplicate entries if they somehow appear
            else:
                filepaths.add(filepath)

            try:
                # Exclude 'cc' [0] and source file [-1] from compile command
                tu = cindex.TranslationUnit.from_source(
                        filepath,
                        args = list(ccmds.arguments)[1:-1]
                )
                cursor: cindex.Cursor = tu.cursor
                global_identifiers |= get_top_level_decl_locations(cursor)

            except cindex.TranslationUnitLoadError:
                traceback.format_exc()
                print_err(f"Failed to parse TU: {filepath}")

    except cindex.CompilationDatabaseError:
        traceback.format_exc()
        print_err(f"Error parsing {basepath}/compile_commands.json")


    time_end("Global symbol enumeration", start_time)

    return global_identifiers

def read_in_names(rename_txt: str, names: set[str]):
    with open(rename_txt, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            names.add(line.rstrip("\n"))

def write_rename_files(dep_path: str, ccdb: cindex.CompilationDatabase,):
    ''' 
    Dump a list of global_name;line;col names to disk 
    along with a newline seperated file containing just the global names 
    '''
    global_identifiers = get_global_identifiers(dep_path, ccdb)

    # Only produced for debugging purposes
    with open(CONFIG.RENAME_CSV, "w", encoding="utf8") as f:
        f.write("filepath;name;line;column\n")
        for identifier in global_identifiers:
            f.write(f"{identifier.to_csv()}\n")

        for identifier in CONFIG.EXPLICIT_RENAME:
            f.write(f";{identifier};;\n")

    # Used by CBMC when invoked with 'USE_SUFFIX'
    # In this version we strip out any duplicate occurences of the same name
    global_names = set([ g.name for g in global_identifiers ])

    with open(CONFIG.RENAME_TXT, "w", encoding="utf8") as f:
        for name in global_names:
            f.write(f"{name}\n")
        for name in CONFIG.EXPLICIT_RENAME:
            f.write(f"{name}\n")
