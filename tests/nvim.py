#!/usr/bin/env python3
import glob
import subprocess
import sys
import time
sys.path.append('../')

import pynvim, os

# cd ~/.cache/euf/oniguruma-65a9b1aa && NVIM_LISTEN_ADDRESS=/tmp/eufvim  /usr/bin/nvim -n --clean -u ~/Repos/euf/scripts/init.lua -c ":call feedkeys(':lua Rename{filepath = \"/home/jonas/.cache/euf/oniguruma-65a9b1aa/st.c\", name = \"rehash\", line = 314, column = 1 }')" regexec.c; cd -

# /usr/bin/env nvim --embed --headless -n --clean -u /home/jonas/Repos/euf/scripts/init.lua regexec.lua

FILE = "regexec.c"
cwd = "/home/jonas/.cache/euf/oniguruma-65a9b1aa"
INIT_VIM = "/home/jonas/Repos/euf/scripts/init.lua"

def child():
    eufdir = os.getcwd()

    # Create a session
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

def conn():
    eufdir = os.getcwd()
    # Session name can be seen in v:servername

    # Create a session
    os.chdir(cwd)
    print("Opening nvim...")

    p  = subprocess.Popen("/usr/bin/env nvim --listen 127.0.0.1:55511 --headless -n --clean -u /home/jonas/Repos/euf/scripts/init.lua regexec.c".split(" "))

    time.sleep(3)

    nvim = pynvim.attach('tcp', address = "127.0.0.1", port = 55511 )

    print("Overwriting file...")
    nvim.current.buffer[:] = ["This"]
    nvim.command("write!")
    nvim.close()

    p.terminate()

    os.chdir(eufdir)

def exit_me():

    # The socket address can be set on start up with
    # 
    nvim = pynvim.attach("socket", path = "/tmp/eufvim")
    nvim.command("wa!")
    nvim.command("quit")
    nvim.close()

exit_me()
