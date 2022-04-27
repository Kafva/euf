#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
NPROC=$((`nproc` - 1))

print_hdr(){
  for _ in $(seq $COLUMNS); do printf "="; done; printf "\n"
  printf "\t\t$1\n"
  for _ in $(seq $COLUMNS); do printf "="; done; printf "\n"
}

# Current (f9afa950e26) JQ uses 6fa38f4 as their base commit for oniguruma
old_ver=${old_ver:=/home/jonas/.cache/euf/oniguruma-6fa38f40}
new_ver=${new_ver:=/home/jonas/.cache/euf/oniguruma-2b3b9d35}

print_hdr oniguruma

cd $new_ver &&
  # Clean up any traces of goto-cc
  make clean
  git clean -fd --exclude=compile_commands.json 
  git checkout .
  # Rebuild with -g 
  ./configure CFLAGS="-g"  &&
  make -j$NPROC &&

print_hdr jq

# Compile jq with the custom version
cd ~/Repos/jq
  make clean
  ./configure CFLAGS="-g" \
    --with-oniguruma=$new_ver/src/.libs &&
    make -j$NPROC

print_hdr testing


# Check if _ANY_ test fails from the update
make check

# Invoke a test case that uses regex functionality
#input_data=$(mktemp --suffix .json)
#
#echo '[{"offset":0, "length":0, "string":"a", "captures":[]},{"offset":1,
#"length":0, "string":"b", "captures":[]},{"offset":2, "length":0, "string":"c",
#"captures":[]}]' > $input_data
#
#TRACE_FILE=/tmp/jq_trace
#rm -f $TRACE_FILE
#valgrind --tool=callgrind --vgdb=no --callgrind-out-file=$TRACE_FILE \
#  ~/Repos/jq/jq ".[].string |match(\"^[a-z]\")" $input_data
#
## Grep out a list of all functions from oniguruma that were called during 
## the invocation
#grep -in -f ~/Repos/euf/examples/onig/rename.txt $TRACE_FILE | awk '{print $2}'



