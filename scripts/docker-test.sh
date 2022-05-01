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

verify(){
  for f in $RESULTS/*.csv; do
    if echo $f|grep -q cbmc; then
      verify_cbmc $f $EXPECTED/$(basename $f)
    else
      compare $f $EXPECTED/$(basename $f)
    fi
  done
}

./euf.py --config tests/configs/docker.json
echo "=====> Oniguruma <====="
EXPECTED=tests/expected/libonig_6c88_a3c2
RESULTS=results/libonig_6c88_a3c2
verify

./euf.py --config tests/configs/expat_docker.json

echo "=====> Expat <====="
EXPECTED=tests/expected/libexpat_10d3_f178
RESULTS=results/libexpat_10d3_f178
verify
