from os.path import expanduser

from git.repo.base import Repo
from cparser.transform import remove_static_specifiers
from cparser.util import flatten
from cparser.build import dir_has_magic_file

REPO_PATH = f"{expanduser('~')}/Repos/jq"

def test():
    assert( flatten([[1,2],[3,4]]) == [1,2,3,4])

def test_dir_has_elf_binary():
    assert( dir_has_magic_file(f"/usr/local/bin") )
    assert( dir_has_magic_file(REPO_PATH) )
    assert( not dir_has_magic_file(f"{expanduser('~')}/.config/nvim") )

def test_remove_static_specifiers():
    repo = Repo(REPO_PATH)
    repo.git.checkout(".") # type: ignore

    remove_static_specifiers(REPO_PATH)
    # Manual review


