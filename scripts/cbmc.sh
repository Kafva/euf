die(){ echo -e "$1" >&2 ; exit 1; }
TOP_LEVEL_DECLS=/tmp/top_decls.list
OUTFILE=runner

[ -z "$COMMIT_OLD" ] && die "Missing enviroment variables"

rm -f $OUTDIR/$OUTFILE

# --- Config ----
# Passed through env
#	COMMIT_OLD=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
#	COMMIT_NEW=1bd71be9437db6ede501fc88102961423c1ab74c
#	DEP_FILE_NEW=src/regexec.c
#	DEP_FILE_OLD=regexec.c
#	PROJECT_FILE=src/builtin.c
#	
#	DEP_OLD=~/Repos/oniguruma
#	DEP_NEW=/tmp/oniguruma
#	PROJECT=~/Repos/jq
#	OUTDIR=~/Repos/euf/tests
#	DRIVER=$OUTDIR/regexec_driver.c
# ---------------


# We need to re-name all global symbols in the old version with a new suffix
# to avoid duplicates
#
# We can extract all top level symbols with clang.cindex and pass these names to sed for a full resolution 
./euf.py --commit-old $COMMIT_OLD \
 --commit-new $COMMIT_NEW \
 --dep-only $DEP_FILE_NEW \
 --project-only $PROJECT_FILE \
 --dump-top-level-decls \
 --dependency $DEP_OLD $PROJECT > $TOP_LEVEL_DECLS

# TODO: We need to have a copy of both versions of compile_commands.json
cd $DEP_OLD
ORIG_OLD_BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
echo "$ORIG_OLD_BRANCH" | grep -iqE "^[a-z]+$" || die "$PWD: Failed to determine current branch"

git checkout $COMMIT_OLD &> /dev/null

while read -r line; do
	sed -i'' "s/${line}/${line}_old/g" $DEP_FILE_OLD
done < $TOP_LEVEL_DECLS 

OLD_NAME=$(basename ${DEP_FILE_OLD%%.c})_old.bc
NEW_NAME=$(basename ${DEP_FILE_NEW%%.c})_new.bc

# We assume that the first argument is the CC and that the last three arguments are '-o output input'
get_cc_cmds(){
	jq "[.[] | select(.file==\"$1/$2\")][0].arguments[1:-3]|join(\" \")" $1/compile_commands.json | xargs
}

/usr/bin/goto-cc $(get_cc_cmds $DEP_OLD $DEP_FILE_OLD) -o $OUTDIR/$OLD_NAME $DEP_FILE_OLD

# Remove the _old suffixes
git checkout $DEP_FILE_OLD

cd $DEP_NEW
ORIG_NEW_BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
echo "$ORIG_NEW_BRANCH" | grep -iqE "^[a-z]+$" || die "$PWD: Failed to determine current branch"

# Check that we have the expected commit checked out
# TODO: More robust impl in Python later
if [ $(git rev-parse HEAD) != $COMMIT_NEW ]; then
	git checkout $COMMIT_NEW &> /dev/null
fi


/usr/bin/goto-cc $(get_cc_cmds $DEP_NEW $DEP_FILE_NEW) -o $OUTDIR/$NEW_NAME $DEP_FILE_NEW

cd $OUTDIR

/usr/bin/goto-cc -I. -DCBMC $DRIVER $OLD_NAME $NEW_NAME -o $OUTFILE

# Run verification
# http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html
# --function-pointer-restrictions-file tests/regexec_restrict.txt
cbmc ./$OUTFILE --function main --trace \
	--z3 --drop-unused-functions \
	--unwind 4

# For cbmc-viewer:
#--xml-ui > result.xml

cd $DEP_NEW && git checkout $ORIG_NEW_BRANCH &> /dev/null || echo "Failed to switch back to $ORIG_NEW_BRANCH"
cd $DEP_OLD && git checkout $ORIG_OLD_BRANCH &> /dev/null || echo "Failed to switch back to $ORIG_OLD_BRANCH"
