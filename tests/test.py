import filecmp, os
from os.path import expanduser
from cparser import BASE_DIR, CONFIG
from cparser.arg_states import call_arg_states_plugin, get_subdir_tus, join_arg_states_result

from cparser.util import flatten
from cparser.build import dir_has_magic_file
from euf import run

REPO_PATH = f"{expanduser('~')}/Repos/jq"
EXPAT_PATH = f"{expanduser('~')}/Repos/libexpat/expat"
EXPAT_OLD_PATH = f"{expanduser('~')}/.cache/euf/libexpat-90ed5777/expat"
USB_PATH = f"{expanduser('~')}/.cache/euf/libusb-385eaafb/libusb"
TEST_DIR =  f"{BASE_DIR}/tests"
RESULT_DIR = f"{BASE_DIR}/results"

def test():
    assert( flatten([[1,2],[3,4]]) == [1,2,3,4])

def test_dir_has_elf_binary():
    assert( dir_has_magic_file(f"/usr/local/bin") )
    assert( dir_has_magic_file(REPO_PATH) )
    assert( not dir_has_magic_file(f"{expanduser('~')}/.ssh") )

def test_transative_changes():
    ''' Verifies that the transative change set is not empty for a known case '''
    CONFIG.update_from_file(f"{TEST_DIR}/configs/onig_trans_test.json")
    run()
    assert(filecmp.cmp(
        f"{RESULT_DIR}/libonig_7ed8_e8bd/trans_change_set.csv", \
        f"{TEST_DIR}/expected/libonig_7ed8_e8bd_trans_change_set.csv"
    ))

def test_get_source_subdirs():
    expected = [ "examples", "lib", "tests", "tests/benchmark", "xmlwf" ]

    subdirs = get_subdir_tus(EXPAT_PATH)
    assert( set([ key for key in subdirs.keys() ]) ==
            set( [ f"{EXPAT_PATH}/{subdir}" for subdir in  expected ] )
    )

    # Test with source in root
    if os.path.exists(f"{USB_PATH}/compile_commands.json"):
        expected = [ "" ]
        subdirs = get_subdir_tus(USB_PATH)
        assert( set([ key for key in subdirs.keys() ]) ==
                set( [USB_PATH] )
        )

def test_join_arg_states_result():

    function_name = "usage"

    if os.path.exists(EXPAT_OLD_PATH):
        for subdir, subdir_tu in get_subdir_tus(EXPAT_OLD_PATH).items():
            call_arg_states_plugin(EXPAT_OLD_PATH, subdir, subdir_tu, function_name, quiet=True)

    result = join_arg_states_result()
    assert( result[function_name].parameters[1].states == set([0,1,2]) )
