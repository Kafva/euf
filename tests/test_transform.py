from cparser.transform import get_clang_suffix_ccmds


def test_get_clang_suffix_ccmds():
    ccmds = [ "-DHAVE_CONFIG_H", "-D", "DEBUG", "-I.",
            "-I", "/usr/local/include", "-g", "-O2", "-c",
            "-fPIC", "-I/usr/include"
    ]

    out = get_clang_suffix_ccmds(ccmds)

    assert( out  == ["-DHAVE_CONFIG_H", "-D", "DEBUG",
            "-I.", "-I", "/usr/local/include", "-I/usr/include"])
