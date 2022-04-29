#!/usr/bin/env bash
docker run \
  -v /home/jonas/Repos/jq:/home/euf/Repos/jq \
  -v /home/jonas/Repos/oniguruma:/home/euf/Repos/oniguruma \
  -v $PWD/output:/home/euf/euf/results \
  euf --config tests/configs/docker.json

