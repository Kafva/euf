import pynvim, subprocess, os

def test():
    INIT_VIM = "/home/jonas/Repos/euf/scripts/init.lua"
    FILE = "regexec.c"
    cwd = "/home/jonas/.cache/euf/oniguruma-65a9b1aa"
    eufdir = os.getcwd()

    #subprocess.Popen(
    #        f"nvim --headless --listen 127.0.0.1:55566 -n --clean -u {INIT_VIM} {FILE}".split(" "),
    #        cwd = cwd,
    #        shell = True
    #)
    #nvim = pynvim.attach('tcp', address="127.0.0.1", port=55566)

    # Attach to the session
    os.chdir(cwd)
    print("Opening nvim...")
    nvim = pynvim.attach('child', argv =
            f"/usr/bin/env nvim --embed --headless -n --clean -u {INIT_VIM} {FILE}".split(" ")
    )

    print("Overwriting file...")
    nvim.current.buffer[:] = ["This"]
    nvim.command("write")
    nvim.close()


    os.chdir(eufdir)

test()
