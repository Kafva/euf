#!/usr/bin/env bash
OUTFILE=runner

[[ -z "$OUTDIR" || -z "$DEPENDENCY_OLD" || -z "$DEPENDENCY_NEW" || 
   -z "$DRIVER" || -z "$UNWIND" || -z "$SETX" || -z "$NEW_LIB"  || -z "$OLD_LIB" 
]] && die "Missing enviroment variable(s)"

OUTFILE=runner

mkdir -p $OUTDIR
rm -f $OUTDIR/$OUTFILE

$SETX && set -x
cp ./drivers/cprover_builtin_headers.h  $OUTDIR

# TODO: Automate this
#cp $DEPENDENCY_NEW/src/oniguruma.h 	$OUTDIR/oniguruma_new.h
#cp $DEPENDENCY_OLD/oniguruma.h 		$OUTDIR/oniguruma_old.h

# Note that the libraries can become unaccessible if they are compiled with an
# older version of goto-cc compared to the current 
goto-cc -DCBMC -I $OUTDIR \
	$NEW_LIB $OLD_LIB $DRIVER \
 	-o $OUTFILE

cbmc --drop-unused-functions --list-goto-functions $OUTFILE
#cbmc --drop-unused-functions --show-goto-functions $OUTFILE




# Using Z3 tends to take longer compared to the default (MathSAT)
# This works for _1_ unwinding since that drops all conditions
time cbmc ./$OUTFILE --function main \
	--drop-unused-functions \
	--unwind $UNWIND \
	--object-bits 12 --property main.assertion.1

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
