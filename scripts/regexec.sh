#!/usr/bin/env bash
OUTFILE=runner
UNWIND=1

# When we actually integrate the entire library properly we end up in 
# situtations were CBMC fails to terminate

# Seems to hang on:
#	regparse.h:callout_name_table_*


#clang -L~/Repos/oniguruma/src/.libs -lonig -I ~/Repos/oniguruma/src \
#	tests/regexec_driver.c -o $OUTFILE &&
#./$OUTFILE


#goto-cc -DCBMC -L~/Repos/oniguruma/src/.libs -lonig -I ~/Repos/oniguruma/src \
#	tests/regexec_driver.c -o $OUTFILE

goto-cc -DCBMC -I ~/Repos/oniguruma/src \
	tests/regexec_driver.c \
	~/Repos/oniguruma/src/.libs/libonig.a -o $OUTFILE

#cbmc --list-goto-functions $OUTFILE

set -x
time cbmc ./$OUTFILE --function main \
	--z3 --drop-unused-functions \
	--unwind $UNWIND --trace
set +x


