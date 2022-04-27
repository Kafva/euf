#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
NPROC=$((`nproc` - 1))
CHECK_ALL=${CHECK_ALL:=true}

# Current (f9afa950e26) JQ uses 6fa38f4 as their base commit for oniguruma

# We probably haft to downgrade jq to an older version for for any tests to start failing
# Using current JQ (f9afa950e26) and bleeding edge oniguruma (80c0c5c4) does not result in
# any fails
JQ_VER=a9f97e9e
OLD_ONIG_VER=6fa38f40
NEW_ONIG_VER=80c0c5c4

# First version with oniguruma as a submodule
#JQ_VER=02bad4b298d4d2bc
#OLD_ONIG_VER=4ab96b4e
#NEW_ONIG_VER=80c0c5c4

print_hdr(){
  for _ in $(seq $(tput cols)); do printf "="; done; printf "\n"
    printf "\t\t$1\n"
  for _ in $(seq $(tput cols)); do printf "="; done; printf "\n"
}

mk_onig(){
  print_hdr oniguruma
  cd ~/Repos/jq/modules/oniguruma &&
    # Clean up any traces of goto-cc
    make clean
    git checkout $NEW_ONIG_VER 
    git clean -fd --exclude=compile_commands.json 
    # Rebuild with -g 
    ./configure CFLAGS="-g"  &&
    make -j$NPROC
}

mk_jq(){
  print_hdr jq
  cd ~/Repos/jq
    #git checkout $JQ_VER
    make clean
    ./configure CFLAGS="-g" \
      --with-oniguruma=builtin &&
      make -j$NPROC
}


mk_onig &> /dev/null

# Compile jq with the custom version
mk_jq &> /dev/null

print_hdr testing
    

if $CHECK_ALL; then
  # Check if _ANY_ test fails from the update
  make check
else
  # Invoke a test case that uses regex functionality
  input_data=$(mktemp --suffix .json)

  echo '[{"offset":0, "length":0, "string":"a", "captures":[]},{"offset":1,
  "length":0, "string":"b", "captures":[]},{"offset":2, "length":0, "string":"c",
  "captures":[]}]' > $input_data

  TRACE_FILE=/tmp/jq_trace
  rm -f $TRACE_FILE
  valgrind --tool=callgrind --vgdb=no --callgrind-out-file=$TRACE_FILE \
    ~/Repos/jq/jq ".[].string |match(\"^[a-z]\")" $input_data

  # Grep out a list of all functions from oniguruma that were called during 
  # the invocation
  grep -in -f ~/Repos/euf/examples/onig/rename.txt $TRACE_FILE | awk '{print $2}'
fi

printf "jq: $JQ_VER\n"
printf "oniguruma: $OLD_ONIG_VER -> $NEW_ONIG_VER\n"


