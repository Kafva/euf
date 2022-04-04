#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""

#----------------------------#
CMTS=/tmp/commits

pushd ~/Repos/libexpat
git log | awk "/^commit/{print \$2}" > $CMTS

cmt1=$(shuf -n1 $CMTS)
cmt2=$(shuf -n1 $CMTS)

[ "$cmt1" = "$cmt2" ] && die "Try agian..."

date1=$(git show -s --format=%ci $cmt1)
date2=$(git show -s --format=%ci $cmt2)

epoch1=$(date -d "$date1" '+%s')
epoch2=$(date -d "$date2" '+%s')

if [ $epoch1 -gt $epoch2 ]; then
  # 1 is newer
  COMMIT_NEW=$cmt1
  COMMIT_OLD=$cmt2
else
  # 2 is newer
  COMMIT_OLD=$cmt1
  COMMIT_NEW=$cmt2
fi

cat << EOF > /tmp/random.json
{
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW"
}
EOF

popd

echo "$date1 -> $date2"
./euf.py --config \
	<(jq -s '.[0] * .[1]' ./expat/base.json /tmp/random.json)

