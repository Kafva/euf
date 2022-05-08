#!/usr/bin/env bash
# This script has the same functionality as `test_harness.sh` but
# accepts a different input format.
die(){ echo -e "$1" >&2 ; exit 1; }
SILENT=${SILENT:=false}

CONF=/tmp/analyze.json
LIBNAME=$1
FUNC_NAME=$2
COMMIT_OLD=$3
COMMIT_NEW=$4
DIFF=$5

cat << EOF > /tmp/$FUNC_NAME.json
{
  "ONLY_ANALYZE": "$FUNC_NAME",
  "SILENT_IDENTITY_VERIFICATION": $SILENT,
  "USE_EXISTING_DRIVERS": true,
  "ENABLE_RESULT_LOG": false,
  "SILENT_VERIFICATION": $SILENT,
  "SKIP_IMPACT": true,
  "VERBOSITY": 2,
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW",
  "CBMC_TIMEOUT": 30,
  "FORCE_RECOMPILE": false,
  "CBMC_OPTS_STR": "--object-bits 12 --unwind 1 --unwinding-assertions --havoc-undefined-functions",
  "IGNORE_FAILED_IDENTITY": true
}
EOF

jq -rM -s '.[0] * .[1]' examples/base_${LIBNAME}.json /tmp/$FUNC_NAME.json \
                         > $CONF
./euf.py -c $CONF $DIFF
