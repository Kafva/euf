#!/usr/bin/env bash
conf=/tmp/without_cbmc_$RANDOM.json
tmp_conf=$(mktemp --suffix .json)
cat << EOF > $tmp_conf
{
  "FULL": false,
  "RESULTS_DIR": "$PWD/results_impact"
}
EOF

libname=$(basename $1|sed -nE 's/^([^_]*)_.*$/\1/p')
old_commit=$(basename $1|sed -nE 's/.*_([a-z0-9]{8})_.*/\1/p')
new_commit=$(basename $1|sed -nE 's/.*_([a-z0-9]{8})\.json$/\1/p')

grep -q "libusb" <<< "$libname" && libname+="-1.0"

result_subdir="${libname}_${old_commit::4}_${new_commit::4}"

jq -rM -s '.[0] * .[1]' $1 $tmp_conf > $conf
./euf.py -c $conf

# Sanity check results
diff -q "results/$result_subdir/change_set.csv" \
        "results_impact/$result_subdir/change_set.csv" ||
        printf "\033[31m==>\033[0m INCONSISTENT! \033[31m<==\033[0m\n"
