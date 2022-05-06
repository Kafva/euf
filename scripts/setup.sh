#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
warn(){ echo -e "(pytest) \033[33m!>\033[0m $1">&2; }

NPROC=$((`nproc`-1))

if which apt &> /dev/null; then
  # EUF dependencies
  sudo apt-get update -y && sudo apt-get install clang llvm-12 flex bison make \
    curl patch cmake bear -y
  # python3.10
  sudo apt install wget build-essential libreadline-dev \
    libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev \
    libc6-dev libbz2-dev libffi-dev zlib1g-dev -y
  # llvm-13
  sudo apt-get install cmake clang ninja-build -y
elif which pacman &> /dev/null; then
  sudo pacman -Syu --noconfirm --needed clang llvm flex bison make \
    curl patch cmake bear 
else
  die "Unsupported package manager"
fi

# Compile submodules
make -C clang-plugins all
make -C cbmc clean && 
  make -C cbmc install

# Build python3.10 from source
if ! which python3.10 &> /dev/null; then
  cd ~/Repos
    curl -OLs https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tar.xz
    tar -Jxf Python-3.10.0.tar.xz
    cd Python-3.10.0/
    ./configure --enable-optimizations
    sudo make altinstall -j4
fi

# Build llvm-13 from source
if ! clang --version 2>/dev/null | grep -q "version.*13"; then
  [ -d ~/Repos/llvm-project ] ||
    git clone -b release/13.x \
    https://github.com/llvm/llvm-project.git ~/Repos/llvm-project

  [ $(sed -nE 's/MemTotal:\s*(.*) kB/\1/p' /proc/meminfo) -lt 16385440 ] &&
    die "Not enough RAM"

  cd ~/Repos/llvm-project
    mkdir -p build
    cmake -S llvm -B ./build -G "Unix Makefiles" \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_PROJECTS="llvm;clang" &&
    make -C ./build -j$NPROC  &&
    sudo cmake --install ./build --prefix "/usr/local"
fi

# Setup venv
if ! [ -d venv ]; then
  python3.10 -m venv venv
  source ./venv/bin/activate
  pip3 install -r requirements.txt
fi
