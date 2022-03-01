. "$(dirname $0)/helper.sh"

SMACK_DEPS=~/Repos/smack-deps
DEP_NEW=$NEW_DIR/$(basename $DEP_OLD)-${COMMIT_NEW:0:8}
TOP_LEVEL_DECLS=/tmp/top_decls.list
OUTFILE=runnerE.c
UNWIND=10


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

	 OLD_OUT=$(basename ${DEP_FILE_OLD%%.c})_oldE.c
NEW_OUT=$(basename ${DEP_FILE_NEW%%.c})_newE.c

# - - - Old version  - - - #
cd $DEP_OLD
ORIG_OLD_BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
check_branch "$ORIG_OLD_BRANCH" || die "$PWD: Failed to determine current branch"

git checkout $COMMIT_OLD &> /dev/null

while read -r line; do
	sed -i'' "s/${line}/${line}_old/g" $DEP_FILE_OLD
done < $TOP_LEVEL_DECLS 

/usr/bin/clang $(get_cc_cmds $DEP_OLD $DEP_FILE_OLD) -E \
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

/usr/bin/clang $(get_cc_cmds $DEP_NEW $DEP_FILE_NEW) -E \
	-o $OUTDIR/$NEW_OUT $DEP_FILE_NEW || finish

cd $OUTDIR
printf "=> Compiling $OUTFILE\n"
/usr/bin/clang -I. $DRIVER -E -o $OUTFILE || finish

# Run verification
export PATH="$SMACK_DEPS/corral:$SMACK_DEPS/z3/bin:$SMACK_DEPS/boogie:$PATH"

smack $OUTFILE $OLD_OUT $NEW_OUT --check assertions --entry-points main --unroll $UNWIND --solver z3

finish
