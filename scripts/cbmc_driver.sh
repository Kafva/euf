#!/usr/bin/env bash
die(){ 
  echo -e "\033[31m!>\033[0m $1" >&2
  env | grep --color=never -oE "[_a-zA-Z0-9]+=$"
  exit 1
}
output_formatting(){
  esc=$(printf "\033[")
  sed "/^file/d; /^Unwinding/d; /^Not unwinding/d; /^aborting/d
    s/ SUCCESS$/${esc}1;32m SUCCESS${esc}0m/;
    s/ FAILURE/${esc}1;31m FAILURE${esc}0m/;
    "
}
[[ -z "$OUTDIR"      || -z "$DRIVER"        || -z "$CBMC_OPTS_STR"    ||
   -z "$NEW_LIB"     || -z "$OLD_LIB"       || -z "$EUF_ENTRYPOINT"   ||
   -z "$FUNC_NAME"   || -z "$OUTFILE"      || -z "$SHOW_FUNCTIONS"   ||
   -z "$DEP_I_FLAGS"
]] && die "Missing environment variable(s): The following not set:"

cbmc_output=$(mktemp)
rm -f $OUTFILE

# DEP_I_FLAGS contains a the include paths from the NEW version
# of the dependency (with -I flags) that is being analyzed

goto-cc -DCBMC -I $OUTDIR  $DEP_I_FLAGS \
  $NEW_LIB $OLD_LIB $DRIVER \
  -o $OUTFILE 2>&1 | tee $cbmc_output

retval=${PIPESTATUS[0]}

# Print compilation errors if SHOW_ERRORS is set
grep -q  "number of members is different" $cbmc_output && retval=63
grep -qE "names of member [0-9]+ differ"  $cbmc_output && retval=64
[ $retval != 0 ] && exit $retval

# If we use '--drop-unused-functions' we lose pretty much
# all functions (at least according to --list-goto-functions)
IFS=', ' read -r -a CBMC_OPTS <<< "$CBMC_OPTS_STR"

if $SHOW_FUNCTIONS; then
  cbmc ${CBMC_OPTS[@]} --show-goto-functions $OUTFILE 2>&1 |
    grep --color=always -A 5 -i "^$FUNC_NAME" 2>&1 \
    | output_formatting
fi

time cbmc ./$OUTFILE  ${CBMC_OPTS[@]} \
    --function $EUF_ENTRYPOINT \
    --property $EUF_ENTRYPOINT.assertion.1 2>&1 \
    | output_formatting | tee $cbmc_output


# Arbitrary return codes to signify different errors, 
# see cparser/__init__.py
if $(grep -qE "unwinding assertion.*FAILURE" $cbmc_output); then 
  grep -q "Equivalent output:.*SUCCESS" $cbmc_output && exit 73
  grep -q "Equivalent output:.*FAILURE" $cbmc_output && exit 74
fi

grep -q  "no body for function ${FUNC_NAME}$" $cbmc_output && exit 55
grep -q  "no body for function ${FUNC_NAME}_old_b026324c6904b2a$" $cbmc_output && exit 55
grep -q  "0 remaining after simplification" $cbmc_output && exit 53
grep -q  "^VERIFICATION FAILED$" $cbmc_output && exit 54
grep -q  "^VERIFICATION SUCCESSFUL$" $cbmc_output && exit 0
exit 1

