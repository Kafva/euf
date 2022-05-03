import filecmp
from posixpath import expanduser
from euf import run
from src.config import CONFIG
from src.util import remove_files_in
from tests import RESULT_DIR, TEST_DIR, check_cbmc_csv

def test_impact_set():
    '''
    Note that the functions listed in "Affected by changes" will only be explicitly listed
    in the output (with verbosity=0) if the main project actually calls them
    '''
    CONFIG.update_from_file(f"{TEST_DIR}/configs/expat_impact.json")
    remove_files_in(f"{RESULT_DIR}/libexpat_90ed_ef31")
    run(load_libclang=False)

    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/change_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/impact_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/impact_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_90ed_ef31/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_90ed_ef31/trans_change_set.csv" )

def test_usb():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libusb.json")
    remove_files_in(f"{RESULT_DIR}/libusb-1.0_4a55_500c")
    run(load_libclang=False)

    assert filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/change_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/change_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/reduced_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/reduced_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/impact_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/impact_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libusb-1.0_4a55_500c/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/trans_change_set.csv" )

    check_cbmc_csv(f"{RESULT_DIR}/libusb-1.0_4a55_500c/cbmc.csv",
            f"{TEST_DIR}/expected/libusb-1.0_4a55_500c/cbmc.csv"
    )

def test_expat():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/expat.json")
    remove_files_in(f"{RESULT_DIR}/libexpat_10d3_f178")
    run(load_libclang=False)

    assert filecmp.cmp(
        f"{expanduser('~')}/.cache/euf/libexpat-10d34296/expat/.harnesses/ENTROPY_DEBUG.c", \
        f"{TEST_DIR}/expected/ENTROPY_DEBUG.c" )

    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/change_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/reduced_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/reduced_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/impact_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/impact_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libexpat_10d3_f178/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libexpat_10d3_f178/trans_change_set.csv" )

    check_cbmc_csv(f"{RESULT_DIR}/libexpat_10d3_f178/cbmc.csv",
            f"{TEST_DIR}/expected/libexpat_10d3_f178/cbmc.csv"
    )

def test_onig():
    CONFIG.update_from_file(f"{TEST_DIR}/configs/onig.json")
    remove_files_in(f"{RESULT_DIR}/libonig_d3d6_6f8c")
    run(load_libclang=False)

    assert filecmp.cmp(f"{RESULT_DIR}/libonig_d3d6_6f8c/change_set.csv", \
            f"{TEST_DIR}/expected/libonig_d3d6_6f8c/change_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libonig_d3d6_6f8c/reduced_set.csv", \
            f"{TEST_DIR}/expected/libonig_d3d6_6f8c/reduced_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libonig_d3d6_6f8c/impact_set.csv", \
            f"{TEST_DIR}/expected/libonig_d3d6_6f8c/impact_set.csv" )
    assert filecmp.cmp(f"{RESULT_DIR}/libonig_d3d6_6f8c/trans_change_set.csv", \
            f"{TEST_DIR}/expected/libonig_d3d6_6f8c/trans_change_set.csv" )

    check_cbmc_csv(f"{RESULT_DIR}/libonig_d3d6_6f8c/cbmc.csv",
            f"{TEST_DIR}/expected/libonig_d3d6_6f8c/cbmc.csv"
    )

