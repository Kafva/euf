#!/usr/bin/env bash

[[ -z "$OUTDIR" || -z "$DEPENDENCY_OLD" || -z "$DEPENDENCY_NEW" || 
   -z "$DEP_FILE_NEW" || -z "$DEP_FILE_OLD" || -z "$DRIVER" || -z "$UNWIND" ||
   -z "$SETX" ]] && die "Missing enviroment variable(s)"

# We assume that the first argument is the CC and that the last three arguments are '-o output input'
get_cc_cmds(){
	jq "[.[] | select(.file==\"$1/$2\" or .file==\"$2\")][0].arguments[1:-3]|join(\" \")" \
		$1/compile_commands.json | xargs
}
OLD_OUT=$(basename ${DEP_FILE_OLD%%.c})_old.bc
NEW_OUT=$(basename ${DEP_FILE_NEW%%.c})_new.bc
OUTFILE=runner

rm -f $OUTDIR/$OUTFILE

$SETX && set -x
# Compile the old and new version to goto-bin
cd $DEPENDENCY_OLD
/usr/bin/goto-cc $(get_cc_cmds $DEPENDENCY_OLD $DEP_FILE_OLD) \
	-o $OUTDIR/$OLD_OUT $DEP_FILE_OLD

cd $DEPENDENCY_NEW
/usr/bin/goto-cc $(get_cc_cmds $DEPENDENCY_NEW $DEP_FILE_NEW) \
	-o $OUTDIR/$NEW_OUT $DEP_FILE_NEW

# Create a goto binary that includes both versions through a driver/harness
cd $OUTDIR
/usr/bin/goto-cc -I. -DCBMC $OLD_OUT $NEW_OUT $DRIVER -o $OUTFILE


# Run verification
# --function-pointer-restrictions-file tests/regexec_restrict.txt
# --trace
cbmc ./$OUTFILE --function main \
	--z3 --drop-unused-functions \
	--unwind $UNWIND --unwinding-assertions

# For cbmc-viewer:
#--xml-ui > result.xml

$SETX && set +x
true

