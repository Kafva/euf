#!/usr/bin/env bash
verify_cbmc(){
  lhs=$(mktemp --suffix .csv)
  rhs=$(mktemp --suffix .csv)
  # Exclude the runtime field
  cut -d';' -f4 --complement $1 > $lhs
  cut -d';' -f4 --complement $2 > $rhs

  compare $lhs $rhs
}

compare(){
  if diff -q $1 $2 > /dev/null; then
    printf "[\033[32m+\033[0m] SUCCESS $1\n" >&2 
  else
    printf "[\033[31mX\033[0m] FAILURE $1\n" >&2
    cat $1
  fi
}

./euf.py --config tests/configs/docker.json


echo "====================================="

for f in results/libonig_6c88_a3c2/*.csv; do

  if echo $f|grep -q cbmc; then
    verify_cbmc $f tests/expected/libonig_6c88_a3c2/$(basename $f)
  else
    compare $f tests/expected/libonig_6c88_a3c2/$(basename $f)
  fi

done
