import filecmp, os, json
from itertools import zip_longest
from os.path import expanduser
import shutil

from clang import cindex
from git.repo.base import Repo
from cparser import BASE_DIR, CONFIG
from cparser.arg_states import call_arg_states_plugin, get_subdir_tus, join_arg_states_result
from cparser.change_set import git_diff_change_set
from cparser.enumerate_globals import get_global_identifiers

from cparser.util import flatten, mkdir_p
from cparser.build import dir_has_magic_file, patch_ccdb_with_headers
from euf import get_commits, get_source_diffs, run

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
    mkdir_p(outdir)

    if os.path.exists(EXPAT_OLD_PATH):
        for subdir, subdir_tu in get_subdir_tus(EXPAT_OLD_SRC_PATH, EXPAT_OLD_PATH).items():
            call_arg_states_plugin(function_name, outdir, EXPAT_OLD_SRC_PATH, subdir, subdir_tu, quiet=True)

    result = join_arg_states_result( [ EXPAT_OLD_NAME ] )
    # If one includes the lib/tests/ path the expected set increases to [0,1,2]
    assert( result[function_name].parameters[1].states == set([0,2]) )

def test_compdb():
    shutil.copy(f"{TEST_DIR}/expected/jq_compile_base.json",  f"{REPO_PATH}/compile_commands.json") # Setup

    assert(patch_ccdb_with_headers(REPO_PATH))

    # Check that no 'command' entries remain
    with open(f"{REPO_PATH}/compile_commands.json", mode='r', encoding='utf8') as f:
        ccdb = json.load(f)
        assert( not any( [ 'command' in entry for entry in ccdb  ] ) )

def test_git_diff_change_set():

    CONFIG.update_from_file(f"{TEST_DIR}/configs/onig_git_diff.json")
    repo = Repo(ONIG)
    ccdb = cindex.CompilationDatabase.fromDirectory(ONIG_OLD)

    global_identifiers = get_global_identifiers(ONIG_OLD, ccdb)

    (old,new) = get_commits(repo)
    source_diffs = get_source_diffs(old,new)

    change_set = git_diff_change_set(ONIG_OLD, ONIG_NEW, source_diffs, global_identifiers)

    expected_change_set = [
        "make_int_stack",
        "free_int_stack",
        "int_stack_push",
        "swap_node",
        "compile_length_string_node",
        "compile_string_node",
        "compile_range_repeat_node",
        "is_anychar_star_quantifier",
        "compile_length_quantifier_node",
        "compile_quantifier_node",
        "compile_length_quantifier_node",
        "compile_quantifier_node",
        "compile_length_enclose_node",
        "compile_enclose_node",
        "compile_length_anchor_node",
        "compile_length_tree",
        "compile_tree",#
        "renumber_node_backref",
        "renumber_by_map",
        "get_char_length_tree1",
        "get_head_value_node",
        "get_min_len",
        "get_max_len",
        "subexp_recursive_check",
        "subexp_recursive_check_trav",
        "divide_look_behind_alternatives",
        "setup_look_behind",
        "update_string_node_case_fold",
        "expand_case_fold_string_alt",
        "expand_case_fold_string",
        "quantifiers_memory_node_info",
        "set_sub_anchor",
        "print_optimize_info"
    ]

    for returned,expected in zip_longest(change_set["src/regcomp.c"], expected_change_set):
        assert(returned.name == expected)
