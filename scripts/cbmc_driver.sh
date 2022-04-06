#!/usr/bin/env bash
die(){ echo -e "\033[31m!>\033[0m $1" >&2 ; exit 1; }
output_formatting(){
	esc=$(printf "\033[")
	sed "/^file/d; /^Unwinding/d; /^Not unwinding/d; /^aborting/d
		s/ SUCCESS$/${esc}1;32m SUCCESS${esc}0m/;
		s/ FAILURE/${esc}1;31m FAILURE${esc}0m/;
		"
}
[[ -z "$OUTDIR" 		|| -z "$DRIVER"  			|| -z "$CBMC_OPTS_STR"    ||
	 -z "$NEW_LIB"  	|| -z "$OLD_LIB" 			|| -z "$EUF_ENTRYPOINT" 	||
	 -z "$FUNC_NAME"  || -z "$OUTFILE"
]] && die "Missing environment variable(s)"

cbmc_output=$(mktemp)
rm -f $OUTFILE

goto-cc -DCBMC -I $OUTDIR \
	$NEW_LIB $OLD_LIB $DRIVER \
 	-o $OUTFILE || exit $?

# If we use '--drop-unused-functions' we lose pretty much
# all functions (at least according to --list-goto-functions)
IFS=', ' read -r -a CBMC_OPTS <<< "$CBMC_OPTS_STR"

cbmc ${CBMC_OPTS[@]} --show-goto-functions $OUTFILE 2>&1 |
	grep --color=always -A 5 -i "^$FUNC_NAME" 2>&1 \
	| output_formatting

time cbmc ./$OUTFILE  ${CBMC_OPTS[@]} \
		--function $EUF_ENTRYPOINT \
	  --property $EUF_ENTRYPOINT.assertion.1 2>&1 \
    | output_formatting | tee $cbmc_output


rm -f $OUTFILE

# Arbitrary return codes to signify a failed verification (54)
# and a lack of VCCs (53)
grep -q "Generated 0 VCC" $cbmc_output && exit 53
grep -q "^VERIFICATION SUCCESSFUL$" $cbmc_output && exit 0 || exit 54
