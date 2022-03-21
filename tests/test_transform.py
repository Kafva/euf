import os
from cparser import CONFIG, BASE_DIR
from cparser.transform import get_clang_suffix_ccmds, replace_macros_in_file

FILE = f"/home/jonas/Repos/oniguruma/src/st.c"
RENAME_TXT = f"{BASE_DIR}/tests/data/oni_rename.txt"

def test_get_clang_suffix_ccmds():
    ccmds = [ "-DHAVE_CONFIG_H", "-D", "DEBUG", "-I.",
            "-I", "/usr/local/include", "-g", "-O2", "-c",
            "-fPIC", "-I/usr/include"
    ]

    out = get_clang_suffix_ccmds(ccmds)

    assert( out  == ["-DHAVE_CONFIG_H", "-D", "DEBUG",
            "-I.", "-I", "/usr/local/include", "-I/usr/include"])

def test_replace_macros_in_file():
    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': RENAME_TXT,
        'SUFFIX': CONFIG.SUFFIX,
        'SETX': CONFIG.SETX,
        'PLUGIN': CONFIG.PLUGIN,
        'EXPAND': "true"
    })

    global_names = set()

    with open(RENAME_TXT, mode="r",  encoding='utf8') as f:
        for line in f.readlines():
            global_names.add(line.rstrip("\n"))

    replace_macros_in_file(FILE, script_env, BASE_DIR, global_names, dry_run = True)

def test_replace_macros_in_header():
    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': RENAME_TXT,
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

