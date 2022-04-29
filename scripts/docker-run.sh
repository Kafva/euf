#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }

CONF=${CONF:=tests/configs/docker.json}
COMMIT_OLD=$(cat $CONF | jq -rM '.COMMIT_OLD')
COMMIT_NEW=$(cat $CONF | jq -rM '.COMMIT_NEW')

pushd ~/Repos/oniguruma
  git worktree remove $HOME/.cache/euf/oniguruma-${COMMIT_OLD:0:8}
  git branch -D euf-${COMMIT_OLD:0:8}
  git worktree remove $HOME/.cache/euf/oniguruma-${COMMIT_NEW:0:8}
  git branch -D euf-${COMMIT_NEW:0:8}

docker ps --format "{{.Image}}"|grep -q "euf" && die "Already running"

popd

# Build the base image if neccessary
docker images --format "{{.Repository}}" | grep -q "euf-base" ||
  docker build --rm -f Dockerfile.base .

docker build --rm . &&
docker run -it \
  -v /home/jonas/Repos/jq:/home/euf/Repos/jq \
  -v /home/jonas/Repos/oniguruma:/home/euf/Repos/oniguruma \
  -v $PWD/output:/home/euf/euf/results \
  euf --config tests/configs/docker.json

