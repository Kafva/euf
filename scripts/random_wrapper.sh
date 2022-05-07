#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=30
export TIMEOUT=60
export VERBOSITY=-1
export BATCH=true

for _ in $(seq $CASE_CNT); do

  ./scripts/random_case.sh libonig
  ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)

  ./scripts/random_case.sh libexpat
  ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)

  ./scripts/random_case.sh libusb
  ./scripts/run_without_cbmc.sh $(cat /tmp/path_to_prev_random_case)
done
