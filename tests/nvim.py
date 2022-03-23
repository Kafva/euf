import pynvim, os

from cparser import CONFIG

def test():
    FILE = "regexec.c"
    cwd = "/home/jonas/.cache/euf/oniguruma-65a9b1aa"
    eufdir = os.getcwd()

    # Create a session
    os.chdir(cwd)
    print("Opening nvim...")
    nvim = pynvim.attach('child', argv =
            f"/usr/bin/env nvim --embed --headless -n --clean -u {CONFIG.INIT_VIM} {FILE}".split(" ")
    )

    print("Overwriting file...")
    nvim.current.buffer[:] = ["This"]
    nvim.command("write")
    nvim.close()


    os.chdir(eufdir)

test()
