#!/usr/bin/env bash
# Runs only the provided driver
# The first argument can be any driver under expat


# base
COMMIT_OLD=bbdfcfef4747d2d66e81c19f4a55e29e291aa171
COMMIT_NEW=c16300f0bc4318f31f9e27eb2702ddbffe086fea

# rand
# 2016 -> 2019
#COMMIT_NEW=ab89ae73
#COMMIT_OLD=322ca04c


die(){ echo -e "$1" >&2 ; exit 1; }
BASE_DIR=~/Repos/euf

if [ "$1" = ls ]; then
	ls ./expat/drivers/*.c
	exit 0
fi

driver_path=$(printf $BASE_DIR/expat/drivers/$1*.c)
func_name=$(basename ${driver_path%%.c})

[ -f "$driver_path" ] || die "Invalid argument: $driver_path"

cat << EOF > /tmp/$1.json
{
	"DRIVERS": {
	 "$func_name": "$driver_path"
	},
	"USE_PROVIDED_DRIVER": true,

  "COMMIT_NEW": "$COMMIT_NEW",
  "COMMIT_OLD": "$COMMIT_OLD"
}
EOF

$BASE_DIR/euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_DIR/expat/base.json /tmp/$1.json)
