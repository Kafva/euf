import filecmp, os, shutil
from os.path import expanduser

from src import BASE_DIR
from src.config import CONFIG
from src.arg_states import call_arg_states_plugin, \
        get_subdir_tus, join_arg_states_result
from src.types import SourceFile

from src.util import mkdir_p, remove_files_in, rm_f, set_libclang
from src.build import autogen_compile_db, lib_is_gbf, \
    write_canoncial_ccdb
from euf import run
from tests import RESULT_DIR, TEST_DIR

EXPAT_PATH = f"{expanduser('~')}/Repos/libexpat"
EXPAT_SRC_PATH = f"{EXPAT_PATH}/expat"
EXPAT_OLD_PATH = f"{expanduser('~')}/.cache/euf/libexpat-90ed5777"
EXPAT_OLD_SRC_PATH = f"{EXPAT_OLD_PATH}/expat"
EXPAT_OLD_NAME = "libexpat-90ed5777"

def setup():
    ''' Load libclang once for all tests '''
    set_libclang()

    # Create required paths (libexpat-90ed5777)
    conf = f"{TEST_DIR}/configs/libexpat_build_test.json"
    CONFIG.update_from_file(conf)

    if not os.path.exists(EXPAT_OLD_PATH):
        # Create the directory if neccessary
        CONFIG.ENABLE_CBMC = False
        run(load_libclang=False)
        CONFIG.ENABLE_CBMC = True

def test_write_canonical_ccdb():
    CONFIG.PROJECT_DIR = "NO_REPO_NAME_MATCHES_THIS"
    ccdb_path = "/tmp/bad_db.json"
    shutil.copy(f"{TEST_DIR}/expected/bad_db.json", ccdb_path)

    assert write_canoncial_ccdb("/tmp", ccdb_path)

    assert filecmp.cmp(ccdb_path, f"{TEST_DIR}/expected/bad_fixed.json")

def test_isystem_flags():
    isystem_flags = SourceFile.get_isystem_flags(
            f"{EXPAT_SRC_PATH}/lib/xmlparse.c",
            f"{EXPAT_SRC_PATH}/lib"
    )
    assert( isystem_flags == ['-internal-isystem',
        '/usr/lib/clang/13.0.1/include', '-internal-isystem',
        '/usr/local/include'] )

def test_mkdirp():
    make_path = f"{BASE_DIR}/examples/do_not_create"
    mkdir_p(make_path)

    result = os.path.isdir(make_path)
    os.rmdir(make_path)
    assert result

def test_lib_is_gbf():
    assert not lib_is_gbf(f"{TEST_DIR}/expected", "libmatrix_elf.a")
    assert lib_is_gbf(f"{TEST_DIR}/expected", "libmatrix_gbf.a")

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

    subdirs = get_subdir_tus(EXPAT_SRC_PATH)
    assert  set(subdirs) == \
            { f"{EXPAT_SRC_PATH}/{subdir}" for subdir in  expected }

def test_join_arg_states_result():
    function_name = "usage"
    outdir = f"{CONFIG.ARG_STATES_OUTDIR}/{EXPAT_OLD_NAME}"
    conf = f"{TEST_DIR}/configs/libexpat_build_test.json"
    CONFIG.update_from_file(conf)
    mkdir_p(outdir)
    remove_files_in(outdir) # !!

    for subdir, subdir_tu in get_subdir_tus(EXPAT_OLD_SRC_PATH).items():
        call_arg_states_plugin(function_name, outdir,
                subdir, subdir_tu, quiet=True)

    result = join_arg_states_result( [ EXPAT_OLD_NAME ] )
    # If one includes the lib/tests/ path the expected set increases to [0,1,2]
    # The increase is a FP of sorts since the call with (1) is a different 
    # static definition of usage()
    assert result[function_name].parameters[1].states == set([0,2])

def test_remove_dependency_entries_from_project_db():
    CONFIG.PROJECT_DIR = f"{expanduser('~')}/Repos/jq"
    CONFIG.DEPENDENCY_DIR = f"{expanduser('~')}/Repos/oniguruma"
    ccdb_path = "/tmp/compile_commands.json"

    shutil.copy(f"{TEST_DIR}/expected/jq_compile.json", ccdb_path) # Setup

    write_canoncial_ccdb(CONFIG.PROJECT_DIR, ccdb_path)

    assert filecmp.cmp(ccdb_path,
            f"{TEST_DIR}/expected/jq_without_onig_commands.json"
    )

def test_autogen_compile_db():
    rm_f(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json")
    CONFIG.update_from_file(f"{TEST_DIR}/configs/libexpat_build_test.json")
    autogen_compile_db(EXPAT_OLD_SRC_PATH)

    assert filecmp.cmp(f"{EXPAT_OLD_SRC_PATH}/compile_commands.json", \
            f"{TEST_DIR}/expected/expat_compile.json"
    )


