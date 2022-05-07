#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }

TEST_CNT=7

run_trial(){
  local conf=$(mktemp --suffix .json)
  cat << EOF > /tmp/without_cbmc.json
{
  "ENABLE_RESULT_LOG": true,
  "SKIP_IMPACT": false,
  "VERBOSITY": 1,
  "FULL": $FULL,
  "CBMC_TIMEOUT": -1
}
EOF

  jq -rM -s '.[0] * .[1]' $1 /tmp/without_cbmc.json > $conf
  ./euf.py -c $conf
}


rm -rf .con
mkdir -p {results,.con}

#COMMIT_OLD=cc414b64
#COMMIT_NEW=283f024a
#LIBNAME=libexpat

COMMIT_OLD=666647fa
COMMIT_NEW=42ad1d1d
LIBNAME=libusb-1.0


FULL=false

for i in $(seq $TEST_CNT); do
  echo "Running ${i}_$FULL..."
  run_trial .rand/${LIBNAME%%-1.0}_${COMMIT_OLD}_${COMMIT_NEW}.json
  mv results/${LIBNAME}_${COMMIT_OLD:0:4}_${COMMIT_NEW:0:4} .con/${i}_$FULL
  wc -l .con/*/change_set.csv
  sleep 2
  [ $FULL = true ] && FULL=false || FULL=true
done

