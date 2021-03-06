#!/usr/bin/env bash
# !! This script should be ran INSIDE Docker !!

verify_cbmc(){
  local lhs="$RESULTS/lhs_${RANDOM}_$(basename $1)"
  local rhs="$RESULTS/rhs_${RANDOM}_$(basename $2)"
  # Exclude the runtime and harness path fields
  cut -d';' -f4,5 --complement $1 > $lhs
  cut -d';' -f4,5 --complement $2 > $rhs

  compare $lhs $rhs
}

compare(){
  if diff -q $1 $2 > /dev/null; then
    printf "[\033[32m+\033[0m] SUCCESS $1\n" >&2 
  else
    printf "[\033[31mX\033[0m] FAILURE:\n" >&2
    # The results are copied to .docker_results on the main host
    printf "${1//results/.docker_results} "
    grep -q "cbmc.csv$" <<< $rhs && 
      printf "${2//results/.docker_results}\n" ||
      printf "${2}\n"
  fi
}

verify(){
  for f in $RESULTS/*.csv; do
    if grep -q cbmc <<< $f; then
      verify_cbmc $f $EXPECTED/$(basename $f)
    else
      compare $f $EXPECTED/$(basename $f)
    fi
  done
}

./euf.py --config tests/configs/onig_docker.json
echo "=====> Libonig <====="
EXPECTED=tests/expected/libonig_6c88_a3c2
RESULTS=results/libonig_6c88_a3c2
verify

./euf.py --config tests/configs/expat_docker.json
echo "=====> Libexpat <====="
EXPECTED=tests/expected/libexpat_10d3_f178
RESULTS=results/libexpat_10d3_f178
verify


./euf.py --config tests/configs/libusb_docker.json
echo "=====> Libusb <====="
EXPECTED=tests/expected/libusb-1.0_4a55_500c
RESULTS=results/libusb-1.0_4a55_500c
verify
