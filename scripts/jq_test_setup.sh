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

# Create trace.o
cd ~/Repos/euf &&
  gcc -g -finstrument-functions -ldl -rdynamic trace.c -c

print_hdr oniguruma

cd $new_ver &&
  # Clean up any traces of goto-cc
  make clean
  git clean -fd --exclude=compile_commands.json 
  git checkout .
  # Rebuild with tracing enabled
  ./configure CFLAGS="-finstrument-functions -ldl -rdynamic"  &&
  make -j$NPROC &&
  # Add the tracing functions to the library
  ar r src/.libs/libonig.a ~/Repos/euf/trace.o

print_hdr jq

#LD_LIBRARY_PATH="$LIBRARY_PATH:$new_ver/src/.libs" \
#LIBRARY_PATH="$LIBRARY_PATH:$new_ver/src/.libs" make LDFLAGS="-all-static" -j$NPROC

# Compile jq with the custom version
cd ~/Repos/jq
  make clean
  ./configure CFLAGS="-finstrument-functions -ldl -rdynamic" \
    --with-oniguruma=$new_ver/src/.libs &&
    make -j$NPROC

print_hdr testing

# Invoke a test case that uses regex functionality
# and verify that a log is created
input_data=$(mktemp --suffix .json)

echo '[{"offset":0, "length":0, "string":"a", "captures":[]},{"offset":1,
"length":0, "string":"b", "captures":[]},{"offset":2, "length":0, "string":"c",
"captures":[]}]' > $input_data

rm -f /tmp/jq_trace
TRACE_LOGFILE=/tmp/jq_trace ~/Repos/jq/jq ".[].string |match(\"^[a-z]\")" $input_data
cat /tmp/jq_trace

