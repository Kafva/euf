#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=30
export TIMEOUT=60
export VERBOSITY=-1
export BATCH=true

INCONSISTENT=0
PREV_RAND_CASE=/tmp/path_to_prev_random_case

run_trial(){
  ./scripts/random_case.sh $1
  if ! ./scripts/run_without_cbmc.sh $(cat $PREV_RAND_CASE); then
      printf "\033[31m==>\033[0m INCONSISTENT! \033[31m<==\033[0m\n"
      INCONSISTENT=$((INCONSISTENT+1))
  fi

  # Run with REDUCE_NO_VCC active
  conf=/tmp/without_cbmc_$RANDOM.json
  tmp_conf=$(mktemp --suffix .json)
  cat << EOF > $tmp_conf
{
  "RESULTS_DIR": "$PWD/results_novccs",
  "REDUCE_NO_VCCS": true
}
EOF

  jq -rM -s '.[0] * .[1]' $(cat $PREV_RAND_CASE) $tmp_conf > $conf
   ./euf.py -c $conf
}

for _ in $(seq $CASE_CNT); do
  run_trial libonig
  run_trial libexpat
  run_trial libusb
done

echo "=> Inconsistent results: $INCONSISTENT"
