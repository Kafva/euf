die(){ echo -e "$1" >&2 ; exit 1; }

COMMIT_OLD=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
COMMIT_NEW=1bd71be9437db6ede501fc88102961423c1ab74c
DEP_FILE_NEW=src/regexec.c
DEP_FILE_OLD=regexec.c
PROJECT_FILE=src/builtin.c

DEP_OLD=~/Repos/oniguruma
DEP_NEW=/tmp/oniguruma
PROJECT=~/Repos/jq

TOP_LEVEL_DECLS=/tmp/top_decls.list
OUTDIR=~/Repos/euf/tests
DRIVER=~/Repos/euf/tests/regexec_driver.c
OUTFILE=main

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
BRANCH=$(git branch | grep "^\*" | awk '{print $2}')
echo "$BRANCH" | grep -iqE "^[a-z]+$" || die "Failed to determine current branch"

git checkout $COMMIT_OLD &> /dev/null

while read -r line; do
	sed -i'' "s/${line}/${line}_old/g" $DEP_FILE_OLD
done < $TOP_LEVEL_DECLS 

OLD_NAME=$(basename ${DEP_FILE_OLD%%.c})_old.bc
NEW_NAME=$(basename ${DEP_FILE_NEW%%.c})_new.bc

/usr/bin/goto-cc \
	-DHAVE_CONFIG_H \
	-I. -I/usr/local/include -Wall -g -O2 -c \
	-o $OUTDIR/$OLD_NAME \
	$DEP_FILE_OLD

# Remove the _old suffixes
git checkout $DEP_FILE_OLD

cd $DEP_NEW

/usr/bin/goto-cc -I. -I.. -Wall -g -O2 -c \
	-DHAVE_CONFIG_H \
	-o $OUTDIR/$NEW_NAME \
	$DEP_FILE_NEW

cd $OUTDIR

/usr/bin/goto-cc -I. -DCBMC \
	$DRIVER $OLD_NAME $NEW_NAME \
	-o $OUTFILE

# Run verification
# http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html
# --function-pointer-restrictions-file tests/regexec_restrict.txt
cbmc ./$OUTFILE --function main --trace \
	--z3 --drop-unused-functions \
	--unwind 4

# For cbmc-viewer:
#--xml-ui > result.xml

cd $DEP_OLD && git checkout $BRANCH &> /dev/null || echo "Failed to switch back to $BRANCH"
