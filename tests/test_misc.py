import filecmp, os, json, shutil
from itertools import zip_longest
from os.path import expanduser

from clang import cindex

from src import BASE_DIR
from src.config import CONFIG
from src.arg_states import call_arg_states_plugin, \
        get_subdir_tus, join_arg_states_result

from src.util import flatten, mkdir_p, remove_files_in, rm_f
from src.build import autogen_compile_db, lib_is_gbf, patch_ccdb_with_headers, patch_old_bear_db
from euf import run
from tests import RESULT_DIR, TEST_DIR

EXPAT_PATH = f"{expanduser('~')}/Repos/libexpat"
EXPAT_SRC_PATH = f"{EXPAT_PATH}/expat"
EXPAT_OLD_PATH = f"{expanduser('~')}/.cache/euf/libexpat-90ed5777"
EXPAT_OLD_SRC_PATH = f"{EXPAT_OLD_PATH}/expat"
EXPAT_OLD_NAME = "libexpat-90ed5777"


def check_cbmc_csv(path1:str, path2:str):
    with open(path1, mode='r', encoding='utf8' ) as f1:
        with open(path2, mode ='r', encoding='utf8') as f2:
            for line1,line2 in zip_longest(f1.readlines(), f2.readlines()):
                # The runtime field may differ
                split1 = line1.split(";")
                del split1[3]
                split2 = line2.split(";")
                del split2[3]
                assert(''.join(split1) == ''.join(split2))

def setup():
    ''' Load libclang once for all tests '''
    if not os.path.exists(CONFIG.LIBCLANG):
        if not os.path.exists(CONFIG.FALLBACK_LIBCLANG):
            assert(False)
        else:
            CONFIG.LIBCLANG = CONFIG.FALLBACK_LIBCLANG

    cindex.Config.set_library_file(CONFIG.LIBCLANG)

def test_flatten():
    assert( flatten([[1,2],[3,4]]) == [1,2,3,4])

def test_patch_old_bear_db():
    ccdb_path = "/tmp/old_bear.json"
    shutil.copy(f"{TEST_DIR}/expected/old_bear.json", ccdb_path)
    patch_old_bear_db(ccdb_path)
    assert(filecmp.cmp(ccdb_path,f"{TEST_DIR}/expected/old_fixed.json"))

def test_mkdirp():
    make_path = f"{BASE_DIR}/examples/expat/cases/2"
    mkdir_p(make_path)

    result = os.path.isdir(make_path)
    os.rmdir(make_path)
    assert(result)

def test_lib_is_gbf():
    assert(not lib_is_gbf(f"{TEST_DIR}/expected", "libmatrix_elf.a"))
    assert(lib_is_gbf(f"{TEST_DIR}/expected", "libmatrix_gbf.a"))

def test_transitive_changes():
    ''' Verifies that the transative change set is not empty for a known case '''
    CONFIG.update_from_file(f"{TEST_DIR}/configs/onig_trans_test.json")
    run(load_libclang=False)
    assert(filecmp.cmp(
        f"{RESULT_DIR}/libonig_7ed8_e8bd/trans_change_set.csv", \
        f"{TEST_DIR}/expected/libonig_7ed8_e8bd_trans_change_set.csv"
    ))

def test_get_source_subdirs():
    usb_path = f"{expanduser('~')}/.cache/euf/libusb-385eaafb/libusb"
    expected = [ "lib", "xmlwf" ]
    CONFIG.EXCLUDE_REGEXES = ["expat/tests/.*", "expat/examples/.*"]

    subdirs = get_subdir_tus(EXPAT_SRC_PATH, EXPAT_PATH)
    assert( set([ key for key in subdirs.keys() ]) ==
            set( [ f"{EXPAT_SRC_PATH}/{subdir}" for subdir in  expected ] )
    )

    # Test with source in root
    assert(os.path.exists(f"{usb_path}/compile_commands.json"))

    expected = [ "" ]
    subdirs = get_subdir_tus(usb_path, usb_path)
    assert( set([ key for key in subdirs.keys() ]) ==
            set( [usb_path] )
    )

def test_join_arg_states_result():
    function_name = "usage"
    outdir = f"{CONFIG.ARG_STATES_OUTDIR}/{EXPAT_OLD_NAME}"
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libexpat_build_test.json")
    mkdir_p(outdir)
    remove_files_in(outdir) # !!

    if os.path.exists(EXPAT_OLD_PATH):
        for subdir, subdir_tu in get_subdir_tus(EXPAT_OLD_SRC_PATH, EXPAT_OLD_PATH).items():
            call_arg_states_plugin(function_name, outdir, EXPAT_OLD_SRC_PATH, subdir, subdir_tu, quiet=True)

    result = join_arg_states_result( [ EXPAT_OLD_NAME ] )
    # If one includes the lib/tests/ path the expected set increases to [0,1,2]
    # The increase is a FP of sorts since the call with (1) is a different 
    # static definition of usage()
    assert( result[function_name].parameters[1].states == set([0,2]) )

def test_compdb():
    jq_path = f"{expanduser('~')}/Repos/jq"
    shutil.copy(f"{TEST_DIR}/expected/jq_compile_base.json",  f"{jq_path}/compile_commands.json") # Setup

    assert(patch_ccdb_with_headers(jq_path))

    # Check that no 'command' entries remain
    with open(f"{jq_path}/compile_commands.json", mode='r', encoding='utf8') as f:
        ccdb = json.load(f)
        assert(not any( [ 'command' in entry for entry in ccdb ] ))

def test_autogen_compile_db():
    rm_f(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json")
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libexpat_build_test.json")
    autogen_compile_db(EXPAT_OLD_SRC_PATH)

    assert(filecmp.cmp(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json", \
            f"{TEST_DIR}/expected/expat_compile.json" )
    )


