#!/usr/bin/env bash
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
        autoreconf -vfi && ./configure && make -j$((`nproc`-1))
    popd;popd
  fi
}

clone_repo(){
  [ -d "$2" ] || 
    git clone https://github.com/$1.git "$2"
}

dl(){
  local repo=$1
  clone_repo kkos/oniguruma        $repo/oniguruma
  clone_repo libexpat/libexpat     $repo/libexpat
  clone_repo libusb/libusb         $repo/libusb

  clone_repo stedolan/jq           $repo/jq
  clone_repo airspy/airspyone_host $repo/airspy
  get_jabberd2                     $repo/jabberd-2.7.0
  fix_jq                           $repo/jq

  if ! [ -f $repo/airspy/compile_commands.json ]; then
    cd $repo/airspy
      # The 'CMAKE_EXPORT_COMPILE_COMMANDS' option uses 'command'
      # instead of arguments for each entry so we use bear instead
      rm -rf build
      mkdir -p build
      cmake -B build -S . -DINSTALL_UDEV_RULES=OFF &&
        bear -- make -C build -j$NPROC
    cd -
  fi
}

if which apt &> /dev/null; then
  sudo apt-get update -y && 
    sudo apt-get install -y libidn11-dev libudns-dev libgsasl7-dev \
      cmake libusb-1.0-0-dev pkg-config libudev-dev
elif which pacman &> /dev/null; then
  sudo pacman -Syu --noconfirm libidn udns gsasl cmake \
    libusb-1.0-0-dev pkg-config 
else
  die "Unsupported package manager"
fi

# Clone all projects into ~/Repos, for running EUF natively and
# into ~/Repos/.docker for analysis in Docker
mkdir -p ~/Repos/.docker

dl ~/Repos
dl ~/Repos/.docker

# The paths generated in the ccdb for jabberd and airspy will be correspond
# to the host path, /home/$USER/Repos/.docker, and need to be patched 
# into /home/euf/Repos, the mountpoint inside the container
sed -E -i'' "s@Repos/\.docker@Repos@g; s@$USER@euf@g" \
  ~/Repos/.docker/jabberd-2.7.0/compile_commands.json
sed -E -i'' "s@Repos/\.docker@Repos@g; s@$USER@euf@g" \
  ~/Repos/.docker/airspy/compile_commands.json
