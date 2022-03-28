#!/usr/bin/env bash
die(){ echo -e "\033[31m!>\033[0m $1" >&2 ; exit 1; }
[[ -z "$OUTDIR" || -z "$DRIVER" || -z "$UNWIND" || 
	-z "$SETX" || -z "$NEW_LIB"  || -z "$OLD_LIB" 
]] && die "Missing enviroment variable(s)"

OUTFILE=runner

mkdir -p $OUTDIR
rm -f $OUTFILE

$SETX && set -x
#echo $OUTDIR
#cp ./drivers/cprover_builtin_headers.h  						$OUTDIR
cp ~/.cache/euf/libexpat-c16300f0/expat/lib/expat{_external.h,.h} 	$OUTDIR/
# TODO: Not needed
cp ~/.cache/euf/libexpat-bbdfcfef/expat/lib/expat.h 								$OUTDIR/expat_old.h
cp ~/.cache/euf/libexpat-bbdfcfef/expat/lib/expat_external.h 				$OUTDIR/expat_external_old.h
sed -i'' -E 's/expat_external.h/expat_external_old.h/g' $OUTDIR/expat_external.h

# ???
# goto-harness --harness-type call-function --function euf_main  --harness-function-name harness_entry  runner runner_harness.c

# Note that the libraries can become unaccessible if they are compiled with an
# older version of goto-cc compared to the current 
#
# If the compilation fails, verify that the symbols in the old library are 
# actually renamed:
#	cbmc --list-goto-functions $OLD_LIB
#goto-cc -DCBMC -I $(dirname $(dirname $NEW_LIB)) \
#	$NEW_LIB $OLD_LIB $DRIVER \
# 	-o $OUTFILE

goto-cc -DCBMC -I $OUTDIR \
	$NEW_LIB $OLD_LIB $DRIVER \
 	-o $OUTFILE

# If we use '--drop-unused-functions' we lose getDebugLevel()
# We still have $link versions but as soon as we try to invoke them
# they dissapear ('body not available')

fnc_name=XML_ErrorString
#fnc_name=poolBytesToAllocateFor
#fnc_name=matrix_init

#cbmc --unwind $UNWIND --object-bits 24 --list-goto-functions $OUTFILE |
#	grep --color=always -C 5 -i $fnc_name

#cbmc --object-bits 12  --show-goto-functions $OUTFILE |
#	grep --color=always -C 100 -i $fnc_name

time cbmc ./$OUTFILE --function euf_main \
	--unwind $UNWIND \
	--object-bits 12 --property euf_main.assertion.1 #--compact-trace



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
