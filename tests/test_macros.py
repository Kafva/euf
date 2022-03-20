'''
Note: the tests will fail if /tmp/rename.yml does not exist
'''
import os
from cparser import BASE_DIR, CONFIG
from cparser.macros import get_macros_from_file, \
        write_macro_stub_file, replace_macros_in_file

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

    global_names = set()

    with open(CONFIG.RENAME_TXT, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            global_names.add(line.rstrip("\n"))

    replace_macros_in_file(FILE, script_env, BASE_DIR, global_names, dry_run = True)

