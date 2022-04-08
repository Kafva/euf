#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""

#----------------------------#
CMTS=/tmp/commits
LOW_LIMIT=$(date -d "2020-01-01" '+%s')

#BASE_CONF=./tests/configs/onig_base.json
#DEP_DIR=~/Repos/oniguruma
#LIBNAME=libonig

BASE_CONF=./expat/base.json
DEP_DIR=~/Repos/libexpat
LIBNAME=libexpat

pushd $DEP_DIR
git log | awk "/^commit/{print \$2}" > $CMTS

get_pair(){
  cmt1=$(shuf -n1 $CMTS)
  cmt2=$(shuf -n1 $CMTS)
  [ "$cmt1" = "$cmt2" ] && die "Try agian..."

  date1=$(git show -s --format=%ci $cmt1)
  date2=$(git show -s --format=%ci $cmt2)

  epoch1=$(date -d "$date1" '+%s')
  epoch2=$(date -d "$date2" '+%s')
}

get_pair

while [[ $LOW_LIMIT -ge $epoch1 || $LOW_LIMIT -ge $epoch2 ]]; do
  get_pair
done


if [ $epoch1 -gt $epoch2 ]; then
  # 1 is newer
  COMMIT_NEW=$cmt1
  DATE_NEW=$date1

  COMMIT_OLD=$cmt2
  DATE_OLD=$date2
else
  # 2 is newer
  COMMIT_OLD=$cmt1
  DATE_OLD=$date1

  COMMIT_NEW=$cmt2
  DATE_NEW=$date2
fi

echo "=== $DATE_OLD -> $DATE_NEW ==="

cat << EOF > /tmp/random.json
{
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW",
  "QUIET_BUILD": true
}
EOF

popd

mkdir -p .rand

# Save the config if we want to run it agian
cat <(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json) > \
  .rand/${COMMIT_OLD::8}_${COMMIT_NEW::8}_$LIBNAME.json

sleep 2

./euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json)


