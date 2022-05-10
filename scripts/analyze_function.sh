#!/usr/bin/env bash
# This script has the same functionality as `test_harness.sh` but
# accepts a different input format.
die(){ echo -e "$1" >&2 ; exit 1; }

CONF=/tmp/analyze.json
LIBNAME=$1
FUNC_NAME=$2
COMMIT_OLD=$3
COMMIT_NEW=$4
DIFF=$5

SILENT=${SILENT:=false}
TRACE=${TRACE:=true}

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
  "FORCE_RECOMPILE": true,
  "CBMC_OPTS_STR": "--object-bits 12 --unwind 1 --trace --havoc-undefined-functions",
  "IGNORE_FAILED_IDENTITY": true
}
EOF

# --unwinding-assertions

jq -rM -s '.[0] * .[1]' examples/base_${LIBNAME}.json /tmp/$FUNC_NAME.json \
                         > $CONF
if $TRACE; then
  output=/tmp/output
  ./euf.py -c $CONF $DIFF &> $output
  sed -E '/^State/d; /^--/d; 
  /^[[:space:]]*$/d; 
  /\s*[a-z0-9A-Z]+=.*/d; 
  /.*\$.*/d;
  /[01]{8}/d;
  /\(\?\)/d
  '  \
  $output
  printf "\033[34m==>\033[0m TRACE \033[34m<==\033[0m\n"
  grep --no-group-separator --color=never -E -B2 "^\s*ret(_old)*=.*" $output
  #grep --no-group-separator --color=never -E -B2 "^\s*bn=.*" $output
  #grep --no-group-separator --color=never -E -B2 "^\s*node=.*" $output
else
  ./euf.py -c $CONF $DIFF
fi
