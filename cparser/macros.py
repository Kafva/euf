import os, re, subprocess, traceback
from typing import Set
from cparser import C_SYMBOL_CHARS, CONFIG, Macro
from cparser.transform import call_clang_suffix_bare

def replace_macros_in_file(source_file: str, script_env: dict[str,str], cwd: str, global_names: Set[str], dry_run: bool = False):
    macros    = get_macros_from_file(source_file)
    stub_file = write_macro_stub_file(source_file, macros)

    # Expand all macros in the stub file
    script_env.update({
        'EXPAND': "true"
    })

    # We will nearly always get errors when parsing a file with
    # macros that have been duct taped togheter
    try:
        call_clang_suffix_bare(stub_file, script_env, cwd)
    except subprocess.CalledProcessError:
        traceback.print_exc()

    # Update the data property of each macro object
    # with the data from the stub file
    updated_macros = update_macros_from_stub(stub_file, macros, global_names)

    # Overwrite the original file with the updated macro data
    update_original_file_with_macros(source_file, updated_macros, dry_run)

def update_original_file_with_macros(source_file: str, macros: list[Macro], dry_run: bool = False):
    original_content = ""

    # Read in the complete content of the original file
    with open(source_file, mode="r", encoding='utf8') as f:
        original_content = f.readlines()

    # Write a new version of the file with the macro ranges from
    # the macro array replaced with the updated versions
    tmp_file = f"/tmp/replace_macro_{os.path.basename(source_file)}"
    linenr = 0

    with open(tmp_file, mode="w", encoding='utf8') as f:
        for macro in macros:
            # Write macro data and update the linenr
            # to the end of the macro to maintain consistency with the
            # original file
            while True:
                # We assume that the macros are given in order
                if macro.start_line == linenr:
                    f.write(macro.text())
                    for _ in range(macro.end_line - macro.start_line):
                        f.write("\n")
                    linenr = macro.end_line + 1
                    break
                else:
                    f.write(original_content[linenr])
                    linenr += 1

        # Write the rest of the content in one go
        if linenr < len(original_content):
            f.writelines( original_content[linenr:] )

    if not dry_run:
        os.replace(tmp_file, source_file)

def update_macros_from_stub(stub_file: str, macros: list[Macro], global_names: Set[str]) -> list[Macro]:
    skip = False
    macro_name = None
    proto_match = None

    updated_macros = []

    with open(stub_file, mode="r", encoding='utf8') as f:
        for line in f.readlines():
            if skip:
                # Skip the line right after a stub prototype
                skip = False
                continue
            elif macro_name:
                # Extract the replaced version of each define statement
                # and update the macros array
                updated_macros[-1].data = line

                # Note that if a parameter to a macro has a name that overlaps with a global
                # (i.e. references to it in the macro get changed) we need to rename the
                # argument in the macro object as well
                for i,arg in enumerate(updated_macros[-1].arguments):
                    if arg in global_names:
                        updated_macros[-1].arguments[i] += CONFIG.SUFFIX

                macro_name = None

            elif (proto_match := re.search(rf"void stub_({C_SYMBOL_CHARS}+)", line)) != None:
                skip = True
                macro_name = proto_match.group(1)

                # We can assume that the order in the stub file and
                # macros array is the same
                updated_macros.append( macros[len(updated_macros)] )
                assert( macro_name == updated_macros[-1].name )

    return updated_macros

def get_macros_from_file(source_file: str) -> list[Macro]:
    '''
    Any #define statement could techincally contain a global symbol
    and we must extract each one into its own file to replace these
    and patch the original file
    '''
    ARGS_REGEX = "[ ,_0-9a-zA-Z]"
    macros = []
    arguments = []
    linenr = 0 # Line numbers are considered to start from 0
    inside_macro = False

    with open(source_file, mode="r", encoding='utf8') as f:
        for line in f.readlines():

            if inside_macro:
                if not re.search(r"\\$", line):
                    macros[-1].end_line = linenr
                    inside_macro = False

                macros[-1].data += line
                linenr += 1
                continue

            # Match: #define name(a,b,c)
            if (macro_match := re.search(rf"^\s*#define\s+({C_SYMBOL_CHARS}+)\(({ARGS_REGEX}+)\)", line)) != None:
                arguments = list(map(lambda arg: arg.strip(),
                    macro_match.group(2).split(",")))

            # Match: #define name ...
            # Note that we do not match #define statements without a 'body'
            elif (macro_match := re.search(rf"^\s*#define\s+({C_SYMBOL_CHARS}+)\s+.+", line)) != None:
                arguments = []

            if macro_match:
                macros.append( Macro(
                    name = macro_match.group(1),
                    arguments = arguments,
                    start_line = linenr,
                    end_line = linenr
                ))
                # Keep on tracking the line number if the line ends with '\'
                if re.search(r"\\$", line) != None:
                    inside_macro = True

                macros[-1].data += line

            linenr += 1

        return macros

def write_macro_stub_file(source_file: str, macros: list[Macro]) -> str:
    '''
    Write a stub file with all of the macros defined one after an other
    followed by stubs on the form
        void stub2(){
            MACRO
        }
    Note: If a macro invokes another macro defined in a seperate file, 
    the expansion won't happen correctly
    '''
    tmp_name = f"/tmp/macros_{os.path.basename(source_file)}"

    with open(tmp_name, mode="w", encoding='utf8') as f:
        for macro in macros:
            f.write(macro.data + "\n")

        for macro in macros:
            f.write(f"void stub_{macro.name}() {{\n")
            # To make parsing easier later, we always have a line not
            # part of the macro right after the stub prototype
            if len(macro.arguments) > 0:
                comma_seperated_args = ','.join(macro.arguments).strip(",")
                f.write("\tchar " + comma_seperated_args + ";\n")
                f.write(f"\t{macro.name}({comma_seperated_args});\n")
            else:
                f.write(f"\n\t{macro.name}\n")

            f.write("}\n\n")

    return tmp_name


