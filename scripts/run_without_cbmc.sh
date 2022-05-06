#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }

TARGET=.results/5

rerun_trial(){
  local libname=${1##lib}
  local conf=$(mktemp --suffix .json)
  cat << EOF > /tmp/without_cbmc.json
{
  "ENABLE_RESULT_LOG": true,
  "SKIP_IMPACT": false,
  "VERBOSITY": 1,
  "COMMIT_OLD": "$2",
  "COMMIT_NEW": "$3",
  "FULL": false
}
EOF

  jq -rM -s '.[0] * .[1]' examples/base_${libname%%-1.0}.json /tmp/without_cbmc.json > $conf
  ./euf.py -c $conf
}

run_trials(){
  local libname=${1%%-1.0}

  for trial in $TARGET/${1}_*; do
    local old_commit=$(basename $trial|sed -nE 's/.*_([a-z0-9]{4})_.*/\1/p')
    local new_commit=$(basename $trial|sed -nE 's/.*_([a-z0-9]{4})$/\1/p')

    # Fetch longer names...
    local conf=$(find .rand -name "${libname}_$old_commit*_$new_commit*" | head -n1)
    old_commit=$(basename $conf|sed -nE 's/.*_([a-z0-9]{8})_.*/\1/p')
    new_commit=$(basename $conf|sed -nE 's/.*_([a-z0-9]{8})\.json$/\1/p')

    rerun_trial $1 $old_commit $new_commit
  done
}

# Iterate over each case in the given directory and run analysis without CBMC on
# the same commits
run_trials libexpat
run_trials libonig
run_trials libusb-1.0


