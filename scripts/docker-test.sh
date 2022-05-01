#!/usr/bin/env bash
./euf.py --config tests/configs/docker.json
for f in results/libonig_6c88_a3c2/*.csv; do
  diff -q $f tests/expected/libonig_6c88_a3c2/$(basename $f) || 
    printf "[\033[31mX\033[0m]: Failed $f\n" >&2
