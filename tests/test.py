import filecmp
from os.path import expanduser
from cparser import BASE_DIR, CONFIG

from cparser.util import flatten
from cparser.build import dir_has_magic_file
from euf import run

REPO_PATH = f"{expanduser('~')}/Repos/jq"
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
    CONFIG.update_from_file(f"{TEST_DIR}/configs/oniguruma.json")
    run()
    assert(filecmp.cmp(
        f"{RESULT_DIR}/libonig_7ed8_e8bd/trans_change_set.csv", \
        f"{TEST_DIR}/expected/libonig_7ed8_e8bd_trans_change_set.csv"
    ))

