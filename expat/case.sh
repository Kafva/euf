#!/usr/bin/env bash
# Runs the base driver for expat with the given commits
BASE_DIR=~/Repos/euf


# base
COMMIT_OLD=bbdfcfef4747d2d66e81c19f4a55e29e291aa171
COMMIT_NEW=c16300f0bc4318f31f9e27eb2702ddbffe086fea

# gen
#COMMIT_OLD=811c41e3b
#COMMIT_NEW=b1d039607

# rand
# 2016 -> 2019
#COMMIT_NEW=ab89ae73
#COMMIT_OLD=322ca04c

cat << EOF > /tmp/$1.json
{
  "COMMIT_NEW": "$COMMIT_NEW",
  "COMMIT_OLD": "$COMMIT_OLD"
}
EOF

$BASE_DIR/euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_DIR/expat/base.json /tmp/$1.json)
