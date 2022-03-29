#!/usr/bin/env bash
die(){ echo -e "\033[31m!>\033[0m $1" >&2 ; exit 1; }
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

# Drop the goto functions in the binary to see if bodies were dropped 
# (in which case analysis cannot continue)
#cbmc ${CBMC_OPTS[@]} --list-goto-functions $OUTFILE |
#	grep --color=always -C 5 -i $FUNC_NAME

cbmc ${CBMC_OPTS[@]} --show-goto-functions $OUTFILE |
	grep --color=always -A 10 -i "^$FUNC_NAME" #; exit 0

time cbmc ./$OUTFILE  ${CBMC_OPTS[@]} \
		--function $EUF_ENTRYPOINT \
	  --property $EUF_ENTRYPOINT.assertion.1

exit 0
