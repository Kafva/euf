#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
cd ~/Repos/main
binary=${binary:=main}

make clean && 
make CC=clang CFLAGS="-g -fxray-instrument -fxray-instruction-threshold=1" main
#make CC=clang main

# Verify that the binary can be instrumented
objdump -h -j xray_instr_map $binary &>/dev/null || 
  die "!> No xray_instr_map section in $binary"

# Create a yaml file that shows the #ID of all functions
# The instrumentation log will only use #IDs for referencing 
#llvm-xray extract --symbolize main > main.yml

# An xray patched binary will work normally unless we provide XRAY_OPTIONS
# Providing these options will create a trace
XRAY_OPTIONS="xray_logfile_base=trace. patch_premain=true xray_mode=xray-basic verbosity=10" ./main

# We can then derive information from the trace with `llvm-xray`
# NOTE: we need to provide the original binary to the --instr_map for
# function names to be visible
#
# NOTE: The instrumentation only catches internal calls, any call made through
# a linked library is not shown
#
# Provided that we trust the impact set, this is actually not an issue since we
# only need to know if a function in the impact set is being invoked
llvm-xray account --instr_map=./main trace*

rm -f trace*

