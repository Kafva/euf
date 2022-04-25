#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
warn(){ echo -e "(pytest) \033[33m!>\033[0m $1">&2; }
clone_repo(){
  [ -d "$2" ] || git clone https://github.com/$1.git "$2"
}

if $(which apt &> /dev/null); then
  # EUF dependencies
  sudo apt-get install clang llvm-12 flex bison make \
    curl patch cmake -y

  # Dependencies for example projects
  sudo apt-get install libidn11-dev libudns-dev libgsasl7-dev -y
fi

# Compile submodules
#make -C clang-plugins all
#make -C cbmc clean && 
#  make -C cbmc install

# Clone all projects
mkdir -p ~/Repos

clone_repo kkos/oniguruma         ~/Repos/oniguruma
clone_repo libexpat/libexpat      ~/Repos/libexpat
clone_repo libusb/libusb          ~/Repos/libusb
clone_repo michaelrsweet/libcups  ~/Repos/libcups
clone_repo stedolan/jq            ~/Repos/jq

if ! [ -e ~/Repos/jq/modules/oniguruma/src/.libs/libonig.so ]; then
  cd ~/Repos/jq
    git submodule update --init --recursive
    cd modules/oniguruma &&
      autoreconf -vfi && ./configure && make -j4
fi

[ -d "$HOME/Repos/jabberd-2.7.0" ] ||
  ./scripts/get_jabberd2.sh

# Build python3.10 from source
if ! $(which python3.10 &> /dev/null); then
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

# Build llvm-13 from source
if ! $(clang --version 2>/dev/null | grep -q "version.*13"); then
  sudo apt-get install cmake clang ninja-build -y

  [ -d ~/Repos/llvm-project ] ||
    git clone -b release/13.x \
    https://github.com/llvm/llvm-project.git ~/Repos/llvm-project

  cd ~/Repos/llvm-project
    mkdir -p build
    cmake -S llvm -B ./build -G Ninja \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_PROJECTS="llvm;clang" &&
    ninja -C ./build &&
    sudo cmake --install ./build --prefix "/usr/local"
fi


# Build bear (with clang-13)
if ! $(which bear &> /dev/null); then
  sudo apt-get install pkg-config libfmt-dev libspdlog-dev \
    nlohmann-json3-dev libgrpc++-dev protobuf-compiler-grpc \
    libssl-dev libprotobuf-dev -y

  mkdir -p bear/build
  cmake -DENABLE_UNIT_TESTS=OFF -DENABLE_FUNC_TESTS=OFF \
    -DCMAKE_CXX_COMPILER=/usr/bin/gcc \
    -DCMAKE_C_COMPILER=/usr/bin/gcc \
    -S bear/source -B bear/build
      make -C bear/build -j$((`nproc`-1)) all
  sudo make -C bear/build install
fi

# Setup venv
if ! [ -d venv ]; then
  python3.10 -m venv venv
  source ./venv/bin/activate
  pip3 install -r requirements.txt
fi
