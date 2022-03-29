#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
BASE_DIR=~/Repos/euf

[ -f "$BASE_DIR/expat/$1.json" ] || die "$usage"

$BASE_DIR/euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_DIR/expat/base.json $BASE_DIR/expat/$1.json)
