#!/usr/bin/env bash
: '''
Generate a driver and run CBMC for a specific function and (new,old) commit pair
The function names are set in this file and the commits are specifeid using
an existing config file (usually one from .rand)
'''
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <cfg.json> <functions...>"
BASE_DIR=$PWD
CONF=/tmp/config.json
DEBUG=${DEBUG:=false}
CONTEXT_LINES=${CONTEXT_LINES:=15}
EXIT=${EXIT:=false}
SHOW_DIFF=${SHOW_DIFF:=false}
PROJ=${PROJ:=libexpat}
SILENT=${SILENT:=true}
SHOW_FUNC=${SHOW_FUNC:=false}

[ -z "$1" ] && die "$usage"

for func_name in $@; do

[ -f "$func_name" ] && continue

rm -f /tmp/none.txt

cat << EOF > /tmp/$func_name.json
{
  "USE_EXISTING_DRIVERS": false,
  "FORCE_RECOMPILE": false,
  "ONLY_ANALYZE": "$func_name",
  "SILENT_IDENTITY_VERIFICATION": $SILENT,
  "SILENT_VERIFICATION": $SILENT,
  "SHOW_FUNCTIONS": $SHOW_FUNC,
  "ENABLE_RESULT_LOG": false,
  "SKIP_IMPACT": true,
  "ENABLE_CBMC": true,
  "TIMEOUT_BLACKLIST_FILE": "/tmp/none.txt",
  "PAUSES": false,
  "VERBOSITY": 1
}
EOF

if $SHOW_DIFF; then
  [ -z "$FILE" ] && die 'Missing FILE in env'

  IDENT="[_0-9A-Za-z]"
  COMMIT_NEW=$(jq -rM ".COMMIT_NEW" "$1")
  COMMIT_OLD=$(jq -rM ".COMMIT_OLD" "$1")

  git diff --color=always -U9000 --no-index \
    ~/.cache/euf/$PROJ-${COMMIT_OLD:0:8}/$FILE \
    ~/.cache/euf/$PROJ-${COMMIT_NEW:0:8}/$FILE \
    | grep -E -m1 -A $CONTEXT_LINES --color=always  \
    "^\s*${IDENT}*\s*${IDENT}*\s*$func_name\(" |
    bat --language diff --style plain
  $EXIT && exit 0
fi

jq -s '.[0] * .[1]' "$1" /tmp/$func_name.json > $CONF

if $DEBUG; then
  # Configure breakpoints etc. in .pdbrc
  python3 -m ipdb $BASE_DIR/euf.py --config $CONF
else
  $BASE_DIR/euf.py --config $CONF
fi

done

