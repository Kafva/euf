#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
SILENT=${SILENT:=true}

CONF=/tmp/analyze.json
FUNC_NAME=$1
COMMIT_OLD=$2
COMMIT_NEW=$3

cat << EOF > /tmp/$FUNC_NAME.json
{
  "ONLY_ANALYZE": "$FUNC_NAME",
  "SILENT_IDENTITY_VERIFICATION": $SILENT,
  "SILENT_VERIFICATION": $SILENT,
  "SKIP_IMPACT": true
}
EOF

jq -rM -s '.[0] * .[1]' /tmp/$FUNC_NAME.json \
                        examples/base_${libname}.json > $CONF

./euf.py -c $CONF
