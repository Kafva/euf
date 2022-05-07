#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=1
export TIMEOUT=-1
export VERBOSITY=-1
export BATCH=true

INCONSISTENT=0

run_trial(){
  ./scripts/random_case.sh $1
  if ! ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case); then
      printf "\033[31m==>\033[0m INCONSISTENT! \033[31m<==\033[0m\n"
      INCONSISTENT=$((INCONSISTENT+1))
  fi
}

for _ in $(seq $CASE_CNT); do
  run_trial libonig
  run_trial libexpat
  run_trial libusb
done

echo "=> Inconsistent results: $INCONSISTENT"
