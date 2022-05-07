#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=10
export TIMEOUT=-1
export VERBOSITY=-1
export BATCH=true

for _ in $(seq $CASE_CNT); do

  #./scripts/random_case.sh libonig
  #./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)

  ./scripts/random_case.sh libexpat
  ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)

  ./scripts/random_case.sh libusb
  ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)
done
