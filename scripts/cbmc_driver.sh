#!/usr/bin/env bash
[[ -z "$OUTDIR" || -z "$DEPENDENCY_OLD" || -z "$DEPENDENCY_NEW" || 
   -z "$DRIVER" || -z "$UNWIND" || -z "$SETX" || -z "$NEW_LIB"  || -z "$OLD_LIB" 
]] && die "Missing enviroment variable(s)"

OUTFILE=runner

mkdir -p $OUTDIR
rm -f $OUTFILE

$SETX && set -x
cp ./drivers/cprover_builtin_headers.h  $OUTDIR

# TODO: Automate this (should not be needed)
#cp $DEPENDENCY_NEW/src/oniguruma.h 	$OUTDIR/oniguruma_new.h
#cp $DEPENDENCY_OLD/oniguruma.h 		$OUTDIR/oniguruma_old.h

# Note that the libraries can become unaccessible if they are compiled with an
# older version of goto-cc compared to the current 
#
# If the compilation fails, verify that the symbols in the old library are 
# actually renamed:
#	cbmc --list-goto-functions $OLD_LIB
goto-cc -DCBMC -I $OUTDIR \
	$NEW_LIB $OLD_LIB $DRIVER \
 	-o $OUTFILE

# If we use '--drop-unused-functions' we lose getDebugLevel()
# We still have $link versions but as soon as we try to invoke them
# they dissapear ('body not available')

fnc_name=poolBytesToAllocateFor

cbmc --object-bits 12 --list-goto-functions $OUTFILE |
	grep --color=always -C 5 -i $fnc_name

cbmc --object-bits 12  --show-goto-functions $OUTFILE |
	grep --color=always -C 100 -i $fnc_name

#time cbmc ./$OUTFILE --function main \
#	--unwind $UNWIND \
#	--object-bits 12 --property main.assertion.1



# Using Z3 tends to take longer compared to the default (MathSAT)
# This works for _1_ unwinding since that drops all conditions
#time cbmc ./$OUTFILE --function main \
#	--drop-unused-functions \
#	--unwind $UNWIND \
#	--object-bits 12 --property main.assertion.1

# We can extract the SMT file with conditions using --outfile


#time cbmc -DLITERAL_DEF -DCBMC $DRIVER --function main \
#	--drop-unused-functions \
#	--unwind 1 \
#	--object-bits 12 --property main.assertion.1

#time cbmc ./runner --function main \
#	--drop-unused-functions \
#	--unwind 1 --z3 \
#	--object-bits 12 --property main.assertion.1

$SETX && set +x

exit 0
