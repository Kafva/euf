#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
BASE_DIR=~/Repos/euf

if [ "$1" = ls ]; then
	ls ./expat/drivers/*.c
	exit 0
fi

driver_path=$(printf ./expat/drivers/$1*.c)
func_name=$(basename ${driver_path%%.c})

[ -f "$driver_path" ] || die "Invalid argument: $driver_path"

cat << EOF > /tmp/$1.json
{
	"DRIVERS": {
	 "$func_name": "$driver_path"
	},
	"USE_PROVIDED_DRIVER": true
}
EOF

$BASE_DIR/euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_DIR/expat/base.json /tmp/$1.json)
