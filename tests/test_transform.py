import os
from cparser import CONFIG, BASE_DIR
from cparser.transform import get_clang_suffix_ccmds, read_in_names, \
        replace_macros_in_file, ensure_abs_path_in_includes

FILE = f"/home/jonas/Repos/oniguruma/src/st.c"
RENAME_TXT = f"{BASE_DIR}/tests/data/oni_rename.txt"

def test_ensure_abs_path_in_includes():
    commands = ['goto-cc', '-E', '-DHAVE_CONFIG_H', '-I.', '-I..', '-DXML_ENABLE_VISIBILITY=1', '-I./../lib', '-Wall', '-Wextra', '-fexceptions', '-fno-strict-aliasing', '-Wmissing-prototypes', '-Wstrict-prototypes', '-pedantic', '-Wduplicated-cond', '-Wduplicated-branches', '-Wlogical-op', '-Wrestrict', '-Wnull-dereference', '-Wjump-misses-init', '-Wdouble-promotion', '-Wshadow', '-Wformat=2', '-Wno-pedantic-ms-format', '-Wmisleading-indentation', '-fvisibility=hidden', '-g', '-O2', '/home/jonas/.cache/euf/libexpat-bbdfcfef/expat/tests/minicheck.c', '-o', '/tmp/E_minicheck.c']


    ensure_abs_path_in_includes(commands)
    assert(commands == ['goto-cc', '-E', '-DHAVE_CONFIG_H', '-I/home/jonas/Repos/euf', '-I/home/jonas/Repos', '-DXML_ENABLE_VISIBILITY=1', '-I/home/jonas/Repos/lib', '-Wall', '-Wextra', '-fexceptions', '-fno-strict-aliasing', '-Wmissing-prototypes', '-Wstrict-prototypes', '-pedantic', '-Wduplicated-cond', '-Wduplicated-branches', '-Wlogical-op', '-Wrestrict', '-Wnull-dereference', '-Wjump-misses-init', '-Wdouble-promotion', '-Wshadow', '-Wformat=2', '-Wno-pedantic-ms-format', '-Wmisleading-indentation', '-fvisibility=hidden', '-g', '-O2', '/home/jonas/.cache/euf/libexpat-bbdfcfef/expat/tests/minicheck.c', '-o', '/tmp/E_minicheck.c'])

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
    rename_txt = f"{BASE_DIR}/tests/data/ssl_rename.txt"
    file = f"/home/jonas/Repos/openssl/include/openssl/err.h"

    script_env = os.environ.copy()
    script_env.update({
        'RENAME_TXT': rename_txt,
        'SUFFIX': CONFIG.SUFFIX,
        'SETX': CONFIG.SETX,
        'PLUGIN': CONFIG.PLUGIN,
        'EXPAND': "true"
    })

    global_names = set()

    read_in_names(rename_txt, global_names)

    replace_macros_in_file(file, script_env, BASE_DIR, global_names, dry_run = True)
