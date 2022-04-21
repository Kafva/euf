#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
clone_repo(){
  [ -d "$2" ] || git clone https://github.com/$1.git $2
}

# Clone all projects
mkdir -p ~/Repos

clone_repo stedolan/jq            ~/Repos/jq
clone_repo kkos/oniguruma         ~/Repos/oniguruma
clone_repo libexpat/libexpat      ~/Repos/libexpat
clone_repo libusb/libusb          ~/Repos/libusb
clone_repo michaelrsweet/libcups  ~/Repos/libcups

[ -d "$HOME/Repos/jabberd-2.7.0" ] ||
  ./scripts/get_jabberd2.sh


if $(uname -a | grep -iq ubuntu); then
  # Build python3.10 from source
  cd ~/Repos
  sudo apt install wget build-essential libreadline-dev \
    libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev \
    libc6-dev libbz2-dev libffi-dev zlib1g-dev -y

  curl -OLs https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tar.xz
  tar -Jxf Python-3.10.0.tar.xz
  cd Python-3.10.0/
  ./configure --enable-optimizations
  sudo make altinstall -j4
fi

# Setup structure needed for pytest

