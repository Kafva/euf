#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
clone_repo(){
  [ -d "$2" ] || git clone https://github.com/$1.git $2
}

# Clone all projects
mkdir -p ~/Repos

clone_repo kkos/oniguruma         ~/Repos/oniguruma
clone_repo libexpat/libexpat      ~/Repos/libexpat
clone_repo libusb/libusb          ~/Repos/libusb
clone_repo michaelrsweet/libcups  ~/Repos/libcups
clone_repo stedolan/jq            ~/Repos/jq


if ! [ -f ~/Repos/jq/modules/oniguruma/src/.libs/libonig.so ]; then
  cd ~/Repos/jq
    git submodule update --init --recursive
    cd modules/oniguruma &&
      autoreconf -vfi && ./configure && make -j4
fi


[ -d "$HOME/Repos/jabberd-2.7.0" ] ||
  ./scripts/get_jabberd2.sh

if ! $(which python3.10 &> /dev/null); then
  # Build python3.10 from source
  sudo apt install wget build-essential libreadline-dev \
    libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev \
    libc6-dev libbz2-dev libffi-dev zlib1g-dev -y

  cd ~/Repos
    curl -OLs https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tar.xz
    tar -Jxf Python-3.10.0.tar.xz
    cd Python-3.10.0/
    ./configure --enable-optimizations
    sudo make altinstall -j4
fi


if ! $(clang --version 2>/dev/null | grep -q "version.*13"); then
  # Build llvm-13 from source
  sudo apt-get install cmake clang ninja-build -y

  clone_repo llvm/llvm-project ~/Repos/llvm-project

  cd llvm-project
    mkdir -p build
    cmake -S llvm -B ./build -G Ninja \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_PROJECTS="llvm;clang" && 
      ninja -C ./build

fi

# Setup structures needed for pytest

