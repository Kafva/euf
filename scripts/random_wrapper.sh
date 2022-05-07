#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=30
export TIMEOUT=60
export BATCH=true

for _ in $(seq $CASE_CNT); do
  ./scripts/random_case.sh libonig
  ./scripts/random_case.sh libexpat
  ./scripts/random_case.sh libusb
done
