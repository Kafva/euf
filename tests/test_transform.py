from cparser.transform import replace_identifiers

def test_replace_identifiers():
    #names = [
    #    "regint",
    #    "gb18030_mbc_to_code",
    #    "OPENSSL_sk_dup",
    #    "DEBUG_GB18030",
    #    "state",
    #    "gb18030_left_adjust_char_head",
    #]
    #replace_identifiers("/home/jonas/Repos/oniguruma/src/gb18030.c", names, "_old")


    names = [
        "myself",
        "n"
    ]
    replace_identifiers("/home/jonas/Repos/euf/tests/data/ex.c", names, "_old")
