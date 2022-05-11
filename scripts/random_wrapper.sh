#!/usr/bin/env bash
# Run with `time`!
CASE_CNT=25
export TIMEOUT=60
export VERBOSITY=-1
export BATCH=true

INCONSISTENT=0
PREV_RAND_CASE=/tmp/path_to_prev_random_case

run_without_cbmc(){
  local conf=/tmp/without_cbmc_$RANDOM.json
  local tmp_conf=$(mktemp --suffix .json)
  cat << EOF > $tmp_conf
{
  "ENABLE_CBMC": false,
  "RESULTS_DIR": "$PWD/results_impact"
}
EOF

  jq -rM -s '.[0] * .[1]' $1 $tmp_conf > $conf
  ./euf.py -c $conf

  # Sanity check results
  if ! diff -q "results/$2/change_set.csv" \
     "results_impact/$2/change_set.csv"; then
  
      printf "\033[31m==>\033[0m INCONSISTENT! \033[31m<==\033[0m\n"
      INCONSISTENT=$((INCONSISTENT+1))
  fi
}

run_trial(){
  local libname=$1
  # Run a random case
  ./scripts/random_case.sh ${libname}
  
  local prev_rand_case_path=$(cat $PREV_RAND_CASE)

  grep -q "libusb" <<< "$libname" && libname+="-1.0"

  local old_commit=$(basename $prev_rand_case_path|
    sed -nE 's/.*_([a-z0-9]{8})_.*/\1/p')
  local new_commit=$(basename $prev_rand_case_path|
    sed -nE 's/.*_([a-z0-9]{8})\.json$/\1/p')
  local result_subdir="${libname}_${old_commit::4}_${new_commit::4}"

  # Run without cbmc (results_impact)
  run_without_cbmc $prev_rand_case_path $result_subdir
}

for _ in $(seq $CASE_CNT); do
  run_trial libonig
  run_trial libexpat
  run_trial libusb
done

echo "=> Inconsistent results: $INCONSISTENT"
