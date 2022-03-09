#!/usr/bin/env bash
OUTFILE=runner

[[ -z "$OUTDIR" || -z "$DEPENDENCY_OLD" || -z "$DEPENDENCY_NEW" || 
   -z "$DRIVER" || -z "$UNWIND" || -z "$SETX" ]] && 
   die "Missing enviroment variable(s)"

OUTFILE=runner

rm -f $OUTDIR/$OUTFILE

set -x
cp ./drivers/cprover_builtin_headers.h  $OUTDIR

# TODO
cp $DEPENDENCY_NEW/src/oniguruma.h 	$OUTDIR/oniguruma_new.h
cp $DEPENDENCY_OLD/oniguruma.h 		$OUTDIR/oniguruma_old.h


goto-cc -DCBMC -I $OUTDIR \
	$DRIVER \
	$NEW/src/.libs/libonig.a \
	$OLD/.libs/libonig.a \
 	-o $OUTFILE


#cbmc --list-goto-functions $OUTFILE

#time cbmc ./$OUTFILE --function main \
#	--z3 --drop-unused-functions \
#	--unwind $UNWIND --trace
set +x


