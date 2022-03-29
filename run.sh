#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
BASE_DIR=~/Repos/euf

if [ "$1" = ls ]; then
	ls ./expat/drivers/*.c
	exit 0
fi

name=$(printf ./expat/drivers/$1*.c)

[ -f "$name" ] || die "Invalid argument: $name"

cat << EOF > /tmp/$1.json
{
	"DRIVER": "$name",
	"FUNC_NAME": "$(basename ${name%%.c})"
}
EOF

$BASE_DIR/euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_DIR/expat/base.json /tmp/$1.json)
