#!/usr/bin/env bash
: '''
Generate a driver and run CBMC for a specific function and (new,old) commit pair
The function names are set in this file and the commits are specifeid using
an existing config file (usually one from .rand)
'''
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <cfg.json>"
BASE_DIR=~/Repos/euf

[ -z "$1" ] && die "$usage"

FUNCTIONS=(
  lookup
)

for func_name in ${FUNCTIONS[@]}; do

cat << EOF > /tmp/$func_name.json
{
  "ONLY_ANALYZE": "$func_name",
  "SILENT_IDENTITY_VERIFICATION": false,
  "SKIP_IMPACT": true,
  "SHOW_FUNCTIONS": true,
  "DIE_ON_ERROR": true
}
EOF

$BASE_DIR/euf.py --config \
  <(jq -s '.[0] * .[1]' "$1" /tmp/$func_name.json )

done

