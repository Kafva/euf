#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""

#----------------------------#
CMTS=/tmp/commits

case "$1" in
  libusb)
    BASE_CONF=./examples/usb/base.json
    DEP_DIR=~/Repos/libusb
    LIBNAME=libusb
    NOT_BEFORE=$(date -d "2020-01-01" '+%s')
    DISTANCE=$(( 24*60*60 * 15))
    NOT_AFTER=$(date -d "2077-01-01" '+%s')
  ;;
  libonig)
    # Oniguruma fails after ~ e8bd631e: Mon Jun 26 12:53:19 2017 +0900
    #
    # We also need to watch out for changes to structs...
    # This seems to be near un-avoidable with oniguruma...
    BASE_CONF=./examples/onig/base.json
    DEP_DIR=~/Repos/oniguruma
    LIBNAME=libonig
    NOT_BEFORE=$(date -d "2017-01-01" '+%s')
    DISTANCE=$(( 24*60*60 * 20))
    NOT_AFTER=$(date -d "2017-06-25" '+%s')
  ;;
  *)
    BASE_CONF=./examples/expat/base.json
    DEP_DIR=~/Repos/libexpat
    LIBNAME=libexpat
    NOT_BEFORE=$(date -d "2020-01-01" '+%s')
    DISTANCE=$(( 24*60*60 * 1000))
    NOT_AFTER=$(date -d "2077-01-01" '+%s')
  ;;
esac


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

while [[ $epoch1 -lt $NOT_BEFORE  || $epoch2 -lt $NOT_BEFORE  ||
         $epoch1 -gt $NOT_AFTER   || $epoch2 -gt $NOT_AFTER   ||
         $((epoch1 - epoch2)) -gt $DISTANCE || 
         $((epoch2 - epoch1)) -gt $DISTANCE
      ]]; do
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

echo "=== $DATE_OLD (${COMMIT_OLD:0:8})-> $DATE_NEW (${COMMIT_NEW:0:8}) ==="

cat << EOF > /tmp/random.json
{
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW",
  "QUIET_BUILD": true
}
EOF

popd

mkdir -p .rand

OUTNAME=.rand/${LIBNAME}_${COMMIT_OLD::8}_${COMMIT_NEW::8}.json

# Save the config if we want to run it agian
cat <(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json) > $OUTNAME
  

printf "Press enter to start...";
while :; do
  read ans
  printf "$ans" | grep -q q && exit
  [ "$ans" = "" ] && break
done

./euf.py --config \
	<(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json)

echo "=> $OUTNAME"

