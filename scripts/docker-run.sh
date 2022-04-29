#!/usr/bin/env bash
# ./euf.py --config /home/euf/configs/docker.json
die(){ echo -e "$1" >&2 ; exit 1; }

CONF=${CONF:=tests/configs/docker.json}
#COMMIT_OLD=$(cat $CONF | jq -rM '.COMMIT_OLD')
#COMMIT_NEW=$(cat $CONF | jq -rM '.COMMIT_NEW')

#pushd ~/Repos/oniguruma
#  git worktree remove $HOME/.cache/euf/oniguruma-${COMMIT_OLD:0:8}
#  git branch -D euf-${COMMIT_OLD:0:8}
#  git worktree remove $HOME/.cache/euf/oniguruma-${COMMIT_NEW:0:8}
#  git branch -D euf-${COMMIT_NEW:0:8}
#popd

docker ps --format "{{.Image}}"|grep -q "euf" && die "Already running"

# Build the base image if neccessary
docker images --format "{{.Repository}}" | grep -q "euf-base" ||
  docker build --rm --tag=euf-base -f Dockerfile.base .

docker build --rm --tag=euf . &&
docker run -it \
  -u euf:root \
  -v /home/jonas/Repos/jq:/home/euf/Repos/jq \
  -v /home/jonas/Repos/oniguruma:/home/euf/Repos/oniguruma \
  -v $PWD/tests/configs:/home/euf/configs \
  --entrypoint /bin/bash euf
  #euf --config /home/euf/configs/docker.json


