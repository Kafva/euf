. "$(dirname $0)/helper.sh"

DEP_NEW=$NEW_DIR/$(basename $DEP_OLD)-${COMMIT_NEW:0:8}
TOP_LEVEL_DECLS=/tmp/top_decls.list
OUTFILE=runner
UNWIND=50

[ -z "$COMMIT_OLD" ] && die "Missing enviroment variables"
rm -f $OUTDIR/$OUTFILE

# We need to re-name all global symbols in the old version with a new suffix
# to avoid duplicates
#
# We can extract all top level symbols with clang.cindex and pass these names to sed for a full resolution 
./euf.py --libclang $LIBCLANG --commit-old $COMMIT_OLD \
 --commit-new $COMMIT_NEW \
 --dep-only $DEP_FILE_NEW \
 --project-only $PROJECT_FILE \
 --dump-top-level-decls \
 --dependency $DEP_OLD $PROJECT > $TOP_LEVEL_DECLS || 
	 { cat $TOP_LEVEL_DECLS ; die "Failed to generate $TOP_LEVEL_DECLS" ; }

OLD_OUT=$(basename ${DEP_FILE_OLD%%.c})_old.bc
NEW_OUT=$(basename ${DEP_FILE_NEW%%.c})_new.bc

# - - - Old version  - - - #
cd $DEP_OLD
ORIG_OLD_BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
check_branch "$ORIG_OLD_BRANCH" || die "$PWD: Failed to determine current branch"

git checkout $COMMIT_OLD &> /dev/null

while read -r line; do
	sed -i'' "s/${line}/${line}_old/g" $DEP_FILE_OLD
done < $TOP_LEVEL_DECLS 

/usr/bin/goto-cc $(get_cc_cmds $DEP_OLD $DEP_FILE_OLD) \
	-o $OUTDIR/$OLD_OUT $DEP_FILE_OLD || finish

# Remove the _old suffixes
git checkout $DEP_FILE_OLD

# - - - New version  - - - #
cd $DEP_NEW
ORIG_NEW_BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
check_branch "$ORIG_NEW_BRANCH" || die "$PWD: Failed to determine current branch"

# Check that we have the expected commit checked out
if [ $(git rev-parse HEAD) != $COMMIT_NEW ]; then
	git checkout $COMMIT_NEW &> /dev/null
fi

/usr/bin/goto-cc $(get_cc_cmds $DEP_NEW $DEP_FILE_NEW) \
	-o $OUTDIR/$NEW_OUT $DEP_FILE_NEW || finish

cd $OUTDIR
printf "=> Compiling $OUTFILE\n"
/usr/bin/goto-cc -I. -DCBMC $OLD_OUT $NEW_OUT $DRIVER -o $OUTFILE || finish

# Run verification
# http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html
# --function-pointer-restrictions-file tests/regexec_restrict.txt
# --trace
set -x
cbmc ./$OUTFILE --function main \
	--z3 --drop-unused-functions \
	--unwind $UNWIND --unwinding-assertions
set +x

# For cbmc-viewer:
#--xml-ui > result.xml
finish
