#!/usr/bin/env bash
die(){ echo -e "\033[31m!>\033[0m $1" >&2 ; exit 1; }
output_formatting(){
	esc=$(printf "\033[")
	sed "/^file/d; 
		s/ SUCCESS$/${esc}1;32m SUCCESS${esc}0m/;
		s/ FAILURE/${esc}1;31m FAILURE${esc}0m/;
		"
}
[[ -z "$OUTDIR" 		|| -z "$DRIVER"  			|| -z "$UNWIND" 		|| 
	 -z "$NEW_LIB"  	|| -z "$OLD_LIB" 			|| -z "$EUF_ENTRYPOINT" 	||
	 -z "$FUNC_NAME"  || -z "$OBJECT_BITS" 	|| -z "$OUTFILE"
]] && die "Missing enviroment variable(s)"

rm -f $OUTFILE

goto-cc -DCBMC -I $OUTDIR \
	$NEW_LIB $OLD_LIB $DRIVER \
 	-o $OUTFILE

# If we use '--drop-unused-functions' we lose pretty much
# all functions (at least according to --list-goto-functions)
CBMC_OPTS=(
	--unwind $UNWIND
	--object-bits $OBJECT_BITS
)

cbmc ${CBMC_OPTS[@]} --show-goto-functions $OUTFILE 2>&1 |
	grep --color=always -A 10 -i "^$FUNC_NAME" 2>&1 \
	| output_formatting

time cbmc ./$OUTFILE  ${CBMC_OPTS[@]} \
		--function $EUF_ENTRYPOINT \
	  --property $EUF_ENTRYPOINT.assertion.1 2>&1 \
		| output_formatting
exit 0
