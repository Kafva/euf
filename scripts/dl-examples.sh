#!/usr/bin/env bash
FULL=${FULL:=false}

get_jabberd2(){
  : '''
  Hacky way of building the compilation database for jabberd2
  Using `autoreconf` with the git version does not work but building
  through the release source does...
  '''
  local target=$1

  [ -d "$1" ] && return

  rm -rf /tmp/{jabberd2,jabberd-2.7.0}
  curl -L https://github.com/jabberd2/jabberd2/releases/download/jabberd-2.7.0/jabberd-2.7.0.tar.gz | 
    tar xzf - -C $(dirname $target)

  git clone -b jabberd-2.7.0 https://github.com/jabberd2/jabberd2.git /tmp/jabberd2

  pushd /tmp/jabberd2 && git switch -c main
  mv .git $target

  pushd $target
    git checkout util/{misc.c,misc.h,pqueue.c,pqueue.h} &&
      ./configure && bear -- make -j$NPROC
  popd;popd
}

fix_jq(){
  if ! [ -e $1/modules/oniguruma/src/.libs/libonig.so ]; then
    pushd $1
      git submodule update --init --recursive
      pushd modules/oniguruma &&
        autoreconf -vfi && ./configure && make -j4
    popd;popd
  fi
}

clone_repo(){
  [ -d "$2" ] || git clone https://github.com/$1.git "$2"
}

if $(which apt &> /dev/null); then
  sudo apt-get update -y && 
    sudo apt-get install libidn11-dev libudns-dev libgsasl7-dev -y

elif $(which pacman &> /dev/null); then
  sudo pacman -Syu libidn udns gsasl --noconfirm 
else
  die "Unsupported package manager"
fi

# Clone all projects
mkdir -p ~/Repos/.docker

clone_repo kkos/oniguruma         ~/Repos/oniguruma
clone_repo libexpat/libexpat      ~/Repos/libexpat
clone_repo libusb/libusb          ~/Repos/libusb
clone_repo michaelrsweet/libcups  ~/Repos/libcups
clone_repo stedolan/jq            ~/Repos/jq

# Seperate repos to avoid errors when running EUF both within and outside docker
clone_repo libexpat/libexpat      ~/Repos/.docker/libexpat

clone_repo stedolan/jq            ~/Repos/.docker/jq
clone_repo kkos/oniguruma         ~/Repos/.docker/oniguruma

get_jabberd2 $HOME/Repos/jabberd-2.7.0
get_jabberd2 $HOME/Repos/.docker/jabberd-2.7.0

fix_jq ~/Repos/jq
fix_jq ~/Repos/.docker/jq

if $FULL; then
  clone_repo bminor/binutils-gdb    ~/Repos/gdb
  # Qemu uses a dedicated build dir (and is huge)
  clone_repo qemu/qemu ~/Repos/qemu
  cd ~/Repos/qemu &&
    ./configure && 
    bear -- make -C build -j$NPROC
  cd -
fi

