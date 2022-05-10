#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <libonig|libexpat|libusb>"
helpStr=""
VERBOSITY=${VERBOSITY:=1}
TIMEOUT=${TIMEOUT:=60}
BATCH=${BATCH:=true}
CMTS=/tmp/commits
MAX_DISTANCE=$(( 24*60*60 * 28))
MIN_DISTANCE=$(( 24*60*60 * 14))

get_pair(){
  cmt1=$(shuf -n1 $CMTS)
  cmt2=$(shuf -n1 $CMTS)

  date1=$(git show -s --format=%ci $cmt1)
  date2=$(git show -s --format=%ci $cmt2)

  epoch1=$(date -d "$date1" '+%s')
  epoch2=$(date -d "$date2" '+%s')
}

abs_distance(){
  local d=$(($1 - $2))
  printf "${d##-}"
}

case "$1" in
  libonig)
    BASE_CONF=./examples/base_onig.json
    DEP_DIR=~/Repos/oniguruma
    LIBNAME=libonig
    # GOTO-bin compilation stops working in oniguruma
    # after 2018-09-20 (69b64fba1735c4)
    # Asserted to work in 2017-04-06 (83aaca7)
    NOT_BEFORE=$(date -d "2017-04-06" '+%s')
    NOT_AFTER=$(date -d "2018-09-19" '+%s')
  ;;
  libexpat)
    BASE_CONF=./examples/base_expat.json
    DEP_DIR=~/Repos/libexpat
    LIBNAME=libexpat
    NOT_BEFORE=$(date -d "2020-04-06" '+%s')
    NOT_AFTER=$(date -d "2077-01-01" '+%s')
  ;;
  libusb)
    BASE_CONF=./examples/base_usb.json
    DEP_DIR=~/Repos/libusb
    LIBNAME=libusb
    NOT_BEFORE=$(date -d "2020-04-06" '+%s')
    NOT_AFTER=$(date -d "2077-01-01" '+%s')
  ;;
  *)
    die "$usage"
  ;;
esac


pushd $DEP_DIR > /dev/null
git log | awk "/^commit/{print \$2}" > $CMTS

get_pair

while [[ $epoch1 -lt $NOT_BEFORE  || $epoch2 -lt $NOT_BEFORE  ||
         $epoch1 -gt $NOT_AFTER   || $epoch2 -gt $NOT_AFTER   ||
         $(abs_distance epoch1 epoch2) -gt $MAX_DISTANCE ||
         $(abs_distance epoch1 epoch2) -lt $MIN_DISTANCE ||
         "$cmt1" = "$cmt2"
      ]]; do
  get_pair
done


if [ $epoch1 -gt $epoch2 ]; then # 1 is newer
  COMMIT_NEW=$cmt1
  DATE_NEW=$date1

  COMMIT_OLD=$cmt2
  DATE_OLD=$date2

else # 2 is newer
  COMMIT_OLD=$cmt1
  DATE_OLD=$date1

  COMMIT_NEW=$cmt2
  DATE_NEW=$date2
fi

echo "=== $DATE_OLD (${COMMIT_OLD:0:8}) -> $DATE_NEW (${COMMIT_NEW:0:8}) === (TIMEOUT=$TIMEOUT)"

cat << EOF > /tmp/random.json
{
  "COMMIT_OLD": "$COMMIT_OLD",
  "COMMIT_NEW": "$COMMIT_NEW",
  "QUIET_BUILD": true,
  "CBMC_TIMEOUT": $TIMEOUT,
  "VERBOSITY": $VERBOSITY
}
EOF

popd > /dev/null

mkdir -p .rand

OUTNAME=.rand/${LIBNAME}_${COMMIT_OLD::8}_${COMMIT_NEW::8}.json

# Save the config if we want to run it again
cat <(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json) > $OUTNAME

if ! $BATCH; then
  printf "Press enter to start...";
  while :; do
    read ans
    printf "$ans" | grep -q q && exit
    [ "$ans" = "" ] && break
  done
fi

./euf.py --config \
  <(jq -s '.[0] * .[1]' $BASE_CONF /tmp/random.json)

# Save the path to the configuration to a static location
printf "$OUTNAME" > /tmp/path_to_prev_random_case
echo "=> $OUTNAME"
