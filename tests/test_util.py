from cparser.util import flatten

def test():
    assert( flatten([[1,2],[3,4]]) == [1,2,3,4])
