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

# Setup structure needed for pytest

