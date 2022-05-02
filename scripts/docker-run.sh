#!/usr/bin/env bash
# ./euf.py --config tests/configs/docker.json
# ./euf.py --config tests/configs/expat_docker.json
# ./euf.py --config examples/libexpat_docker.json
die(){ echo -e "$1" >&2 ; exit 1; }
image_exists(){
  docker images --format "{{.Repository}}" | grep -q "^$1$"
}
docker-id(){ 
  docker ps --format "{{.ID}}  {{.Image}}" | awk '/\s+euf$/{print $1}'
}
CONF=${CONF:=tests/configs/docker.json}
VERIFY=${VERIFY:=false}


if $VERIFY; then
  ENTRYPOINT="--entrypoint /home/euf/euf/scripts/docker-test.sh euf"
else
  ENTRYPOINT="euf --config $CONF"
fi

# Uncomment for debugging
# ENTRYPOINT="--entrypoint /bin/bash euf"

docker ps --format "{{.Image}}"|grep -q "euf" && die "Already running"

# Build the base image if neccessary
image_exists "euf-base" ||
  docker build --rm --tag=euf-base -f Dockerfile.base .

image_exists "euf" ||
  docker build --rm --tag=euf .

# Files edited in vim use a swap file which is copied into place
# on save. Since bind mounts are based on inode numbers we will
# still see the old file in the container after a change from the host. 
# Because of this we cannot live-reload file-mounts, 
# only directory mounts. A background sync job is therefore used for 
# the euf.py script
while :; do
  sleep 2
  docker cp euf.py $(docker-id euf):/home/euf/euf/euf.py
done &

SYNC_PID=$!

# Run with source files mounted to enable live updates
docker run -h euf -it \
  -u euf:root \
  -v $HOME/Repos/.docker/jq:/home/euf/Repos/jq \
  -v $HOME/Repos/.docker/oniguruma:/home/euf/Repos/oniguruma \
  -v $HOME/Repos/.docker/jabberd-2.7.0:/home/euf/Repos/jabberd-2.7.0 \
  -v $HOME/Repos/.docker/libexpat:/home/euf/Repos/libexpat \
  -v $PWD/examples:/home/euf/euf/examples \
  -v $PWD/tests/configs:/home/euf/euf/tests/configs \
  -v $PWD/scripts:/home/euf/euf/scripts \
  -v $PWD/tests:/home/euf/euf/tests \
  -v $PWD/src:/home/euf/euf/src \
  $ENTRYPOINT

kill $SYNC_PID
