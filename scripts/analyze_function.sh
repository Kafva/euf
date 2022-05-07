#!/usr/bin/env bash
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
  "FORCE_RECOMPILE": false
}
EOF

jq -rM -s '.[0] * .[1]' examples/base_${LIBNAME}.json /tmp/$FUNC_NAME.json \
                         > $CONF
./euf.py -c $CONF $DIFF
