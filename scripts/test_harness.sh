#!/usr/bin/env bash
: '''
Generate a driver and run CBMC for a specific function and (new,old) commit pair
The function names are set in this file and the commits are specifeid using
an existing config file (usually one from .rand)
'''
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <cfg.json> <functions...>"
BASE_DIR=~/Repos/euf
CONF=/tmp/config.json
DEBUG=${DEBUG:=false}
CONTEXT_LINES=${CONTEXT_LINES:=15}

[ -z "$1" ] && die "$usage"

for func_name in $@; do

[ -f "$func_name" ] && continue

cat << EOF > /tmp/$func_name.json
{
  "ONLY_ANALYZE": "$func_name"
}
EOF


if [ -n "$SHOW_DIFF" ]; then
  [ -z "$FILE" ] && die 'Missing FILE in env'

  COMMIT_NEW=$(jq -rM ".COMMIT_NEW" "$1")
  COMMIT_OLD=$(jq -rM ".COMMIT_OLD" "$1")

	git diff --color=always -U9000 --no-index \
    ~/.cache/euf/libexpat-${COMMIT_OLD:0:8}/expat/lib/$FILE \
    ~/.cache/euf/libexpat-${COMMIT_NEW:0:8}/expat/lib/$FILE \
		| grep -m1 -A $CONTEXT_LINES --color=always  "$func_name(" | 
    bat --language diff --style plain
	exit 0
fi

jq -s '.[0] * .[1]' "$1" /tmp/$func_name.json > $CONF

if $DEBUG; then
  # Configure breakpoints etc. in .pdbrc
  python3 -m ipdb $BASE_DIR/euf.py --config $CONF
else
  $BASE_DIR/euf.py --config $CONF
fi

done

