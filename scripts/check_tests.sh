#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
RESULT_DIR=./results
EXPECTED_DIR=./tests/expected

verify_cbmc(){
  local lhs="/tmp/lhs_${RANDOM}_$(basename $1)"
  local rhs="/tmp/rhs_${RANDOM}_$(basename $2)"
  # Exclude the runtime and harness path fields
  cut -d';' -f4,5 --complement $1 > $lhs
  cut -d';' -f4,5 --complement $2 > $rhs

  # Note: Docker and the main host will sometimes differ
  # in their results due to being killed by different timeouts
  diff -q $lhs $rhs
}

same(){
    if grep -q cbmc <<< $1; then
      verify_cbmc $1 $2
    else
      diff -q $1 $2
    fi
}

check_results(){
  for csv in $RESULT_DIR/$1/*.csv; do

    local expected="$EXPECTED_DIR/$1/$(basename $csv)"
    [[ -f $expected && -f $csv ]] || continue

    if ! same $csv $expected > /dev/null; then
      while :; do
        printf "\033[31m!>\033[0m $csv $expected\n"
        printf "v(iew)/d(iff)/c(ontinue)/q(uit)/g(ood)..."
        read ans
        case $ans in
          v) git difftool --no-index $csv $expected ;;
          d) diff --color $csv $expected ;;
          g) cp $csv $expected; break ;;
          q) exit ;;
          c) break ;;
        esac
      done
    fi
  done
}

overview(){
  [ -d $RESULT_DIR/$1 ] ||  {
    echo "Missing $RESULT_DIR/$1"; return
  }
  echo "========================"
  for csv in $RESULT_DIR/$1/*.csv; do

    local expected="$EXPECTED_DIR/$1/$(basename $csv)"
    [[ -f $expected && -f $csv ]] || continue

    if ! same $csv $expected > /dev/null; then
        printf "\033[31m!>\033[0m $csv $expected\n"
    else
        printf "\033[32m!>\033[0m $csv $expected\n"
    fi
  done
  echo
}

overview libexpat_90ed_ef31
check_results libexpat_90ed_ef31

overview libusb-1.0_4a55_500c
check_results libusb-1.0_4a55_500c

overview libexpat_10d3_f178
check_results libexpat_10d3_f178

overview libonig_d3d6_6f8c
check_results libonig_d3d6_6f8c

RESULT_DIR=.docker_results

overview libonig_6c88_a3c2
check_results libonig_6c88_a3c2

overview libusb-1.0_4a55_500c
check_results libusb-1.0_4a55_500c

overview libexpat_10d3_f178
check_results libexpat_10d3_f178
