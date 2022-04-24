import filecmp, os, json, shutil
from itertools import zip_longest
from os.path import expanduser

from clang import cindex

from src import BASE_DIR
from src.config import CONFIG
from src.arg_states import call_arg_states_plugin, \
        get_subdir_tus, join_arg_states_result

from src.util import flatten, mkdir_p, remove_files_in, rm_f
from src.build import autogen_compile_db, lib_is_gbf, patch_ccdb_with_headers
from euf import run

TEST_DIR =  f"{BASE_DIR}/tests"
RESULT_DIR = f"{BASE_DIR}/results"

REPO_PATH = f"{expanduser('~')}/Repos/jq"

EXPAT_PATH = f"{expanduser('~')}/Repos/libexpat"
EXPAT_SRC_PATH = f"{expanduser('~')}/Repos/libexpat/expat"

EXPAT_OLD_PATH = f"{expanduser('~')}/.cache/euf/libexpat-90ed5777"
EXPAT_OLD_SRC_PATH = f"{expanduser('~')}/.cache/euf/libexpat-90ed5777/expat"
EXPAT_OLD_NAME = "libexpat-90ed5777"

ONIG = f"{expanduser('~')}/Repos/oniguruma"
ONIG_OLD = f"{expanduser('~')}/.cache/euf/oniguruma-d95bd55c"
ONIG_NEW = f"{expanduser('~')}/.cache/euf/oniguruma-41eb1475"

USB_PATH = f"{expanduser('~')}/.cache/euf/libusb-385eaafb/libusb"

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
    expected = [ "lib", "xmlwf" ]
    CONFIG.EXCLUDE_REGEXES = ["expat/tests/.*", "expat/examples/.*"]

    subdirs = get_subdir_tus(EXPAT_SRC_PATH, EXPAT_PATH)
    assert( set([ key for key in subdirs.keys() ]) ==
            set( [ f"{EXPAT_SRC_PATH}/{subdir}" for subdir in  expected ] )
    )

    # Test with source in root
    assert(os.path.exists(f"{USB_PATH}/compile_commands.json"))

    expected = [ "" ]
    subdirs = get_subdir_tus(USB_PATH, USB_PATH)
    assert( set([ key for key in subdirs.keys() ]) ==
            set( [USB_PATH] )
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
    shutil.copy(f"{TEST_DIR}/expected/jq_compile_base.json",  f"{REPO_PATH}/compile_commands.json") # Setup

    assert(patch_ccdb_with_headers(REPO_PATH))

    # Check that no 'command' entries remain
    with open(f"{REPO_PATH}/compile_commands.json", mode='r', encoding='utf8') as f:
        ccdb = json.load(f)
        assert(not any( [ 'command' in entry for entry in ccdb ] ))

def test_autogen_compile_db():
    rm_f(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json")
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libexpat_build_test.json")
    autogen_compile_db(EXPAT_OLD_SRC_PATH)

    assert(filecmp.cmp(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json", \
            f"{TEST_DIR}/expected/expat_compile.json" )
    )


#== Regression tests ==#

def test_impact_set():
    '''
    Note that the functions listed in "Affected by changes" will only be explicitly listed
    in the output (with verbosity=0) if the main project actually calls them
    '''
    CONFIG.update_from_file(f"{TEST_DIR}/configs/expat_impact.json")
    run(load_libclang=False)

    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/change_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/impact_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/impact_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/trans_change_set.csv" )
    )

def test_usb():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libusb_4a5540a9_500c64ae.json")
    run(load_libclang=False)

    assert(filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/change_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/change_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/reduced_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/reduced_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/impact_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/impact_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/trans_change_set.csv" )
    )

    check_cbmc_csv(f"{RESULT_DIR}/libusb-1.0_4a55_500c/cbmc.csv",
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/cbmc.csv"
    )

def test_expat():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/10d34296_f178826b.json")
    run(load_libclang=False)

    assert(filecmp.cmp(f"{expanduser('~')}/.cache/euf/libexpat-10d34296/expat/.harnesses/ENTROPY_DEBUG.c", \
            f"{TEST_DIR}/expected/ENTROPY_DEBUG.c" )
    )

    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/change_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/reduced_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/reduced_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/impact_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/impact_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/trans_change_set.csv" )
    )

    check_cbmc_csv(f"{RESULT_DIR}/libexpat_10d3_f178/cbmc.csv",
            f"{TEST_DIR}/expected/libexpat_10d3_f178/cbmc.csv"
    )


def test_onig():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libonig_d95bd55c_41eb1475.json")
    run(load_libclang=False)

    assert(filecmp.cmp(f"{RESULT_DIR}/libonig_d95b_41eb/change_set.csv", \
            f"{TEST_DIR}/expected/libonig_d95b_41eb/change_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libonig_d95b_41eb/reduced_set.csv", \
            f"{TEST_DIR}/expected/libonig_d95b_41eb/reduced_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libonig_d95b_41eb/impact_set.csv", \
            f"{TEST_DIR}/expected/libonig_d95b_41eb/impact_set.csv" )
    )
    assert(filecmp.cmp(f"{RESULT_DIR}/libonig_d95b_41eb/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libonig_d95b_41eb/trans_change_set.csv" )
    )

    check_cbmc_csv(f"{RESULT_DIR}/libonig_d95b_41eb/cbmc.csv",
            f"{TEST_DIR}/expected/libonig_d95b_41eb/cbmc.csv"
    )

