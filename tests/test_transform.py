import os
from cparser import BASE_DIR, CONFIG
from cparser.transform import get_clang_suffix_ccmds, get_macros_from_file, \
        write_macro_stub_file, replace_macros_in_file

def test_get_clang_suffix_ccmds():
    ccmds = [ "-DHAVE_CONFIG_H", "-D", "DEBUG", "-I.",
            "-I", "/usr/local/include", "-g", "-O2", "-c",
            "-fPIC", "-I/usr/include"
    ]

    out = get_clang_suffix_ccmds(ccmds)

    assert( out  == ["-DHAVE_CONFIG_H", "-D", "DEBUG",
            "-I.", "-I", "/usr/local/include", "-I/usr/include"])

FILE = f"/home/jonas/Repos/oniguruma/src/st.c"

def test_macros_from_file():
    macros = get_macros_from_file(f"{BASE_DIR}/tests/data/macro.c")

    print(macros,"-------------------")

    assert( macros[0].name == "ADD_DIRECT" and macros[0].start_line == 0 and
            macros[0].end_line == 16 and
            macros[0].arguments == ["table" , "key" , "value" , "hash_val" , "bin_pos"] )

    assert( macros[1].name == "DUPLICATES" and macros[1].start_line == 19 and
            macros[1].end_line == 20 and
            macros[1].arguments == [] )

    assert( macros[2].name == "SIMPLE" and macros[2].start_line == 22 and
            macros[2].end_line == 22 and
            macros[2].arguments == [])

    # The last EMPTY macro should not be included
    assert( len(macros) == 4 )

    macros = get_macros_from_file(FILE)
    print(macros)

def test_write_macro_stub_file():
    macros = get_macros_from_file(FILE)

    write_macro_stub_file(FILE,macros)

def test_replace_macros_in_file():
    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': CONFIG.RENAME_TXT,
        'SUFFIX': CONFIG.SUFFIX,
        'SETX': CONFIG.SETX,
        'PLUGIN': CONFIG.PLUGIN,
        'EXPAND': "true"
    })
    replace_macros_in_file(FILE, script_env, BASE_DIR)
