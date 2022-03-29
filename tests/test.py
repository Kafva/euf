from os.path import expanduser
from cparser.util import flatten
from cparser.build import dir_has_magic_file

def test():
    assert( flatten([[1,2],[3,4]]) == [1,2,3,4])

def test_dir_has_elf_binary():
    assert( dir_has_magic_file(f"/usr/local/bin") )
    assert( dir_has_magic_file(f"{expanduser('~')}/Repos/jq") )
    assert( not dir_has_magic_file(f"{expanduser('~')}/.config/nvim") )
