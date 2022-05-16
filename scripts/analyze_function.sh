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

TRACE=${TRACE:=false}

rm -f /tmp/none.txt

cat << EOF > /tmp/$FUNC_NAME.json
{
  "ONLY_ANALYZE": "$FUNC_NAME",
  "SILENT_IDENTITY_VERIFICATION": true,
  "SILENT_VERIFICATION": false,
  "USE_EXISTING_DRIVERS": false,
  "ENABLE_RESULT_LOG": false,
  "SKIP_IMPACT": true,
  "VERBOSITY": 2,
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW",
  "CBMC_TIMEOUT": 10,
  "FORCE_CCDB_RECOMPILE": false,
  "FORCE_RECOMPILE": true,
  "CBMC_OPTS_STR": "--object-bits 12 --trace --unwind 1 --havoc-undefined-functions",
  "IGNORE_FAILED_IDENTITY": false,
  "ENABLE_STATE_SPACE_ANALYSIS": false,
  "QUIET_BUILD": true
}
EOF

# --unwinding-assertions

jq -rM -s '.[0] * .[1]' examples/base_${LIBNAME}.json /tmp/$FUNC_NAME.json \
                         > $CONF
if $TRACE; then
  output=/tmp/output
  # We don't risk grepping from the trace of the identity verification 
  # provided that the identity verification is successful
  # Running, using --unwinding-assertions causes the --trace option to scale up
  # indefinitely in runtime.
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
  # Grep for interesting variables in the trace
  grep --no-group-separator --color=never -E -B2 "^\s*ret(_old)*=.*" $output

  #== renumber_node_backref ==#
  grep --no-group-separator --color=never -E -B2 "^\s*bn=.*" $output
  grep --no-group-separator --color=never -E -B2 "^\s*node=.*" $output
  grep --no-group-separator --color=never -E -B2 "^\s*node\.u=.*" $output

  #== libusb_release_interface ==#
  #grep --no-group-separator --color=never -E -B2 "^\s*interface_number=.*" $output
else
  ./euf.py -c $CONF $DIFF
fi
