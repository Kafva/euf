die(){ echo -e "$1" >&2 ; exit 1; }
CBMC=true
# Minimial program creation with '-E' (for SMACK) does not seem to be viable

# We need to re-name all global symbols in the old version with a new suffix
# to avoid duplicates
#
# We can extract all top level symbols with clang.cindex and pass these names to sed for a full resolution 
./euf.py --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
 --dep-only src/regexec.c \
 --project-only src/builtin.c \
 --dump-top-level-decls \
 --dependency ../oniguruma ../jq > /tmp/top_decls.list

# TODO: We need to have a copy of both versions of compile_commands.json
cd ~/Repos/oniguruma

BRANCH=$(git branch | awk '{print $2}')
echo "$BRANCH" | grep -iqE "^[a-z]+$" || die "Failed to determine current branch"

git checkout 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 &> /dev/null

cat /tmp/top_decls.list

while read -r line; do
	sed -i'' "s/${line}/${line}_old/g" regexec.c	
done < /tmp/top_decls.list


if $CBMC; then
	/usr/bin/goto-cc -DHAVE_CONFIG_H -I. -I/usr/local/include -Wall -g -O2 -c \
	-o ~/Repos/euf/tests/regexec_old.bc \
	regexec.c

	# Remove the _old suffixes
	git checkout regexec.c

	git checkout 1bd71be9437db6ede501fc88102961423c1ab74c

	/usr/bin/goto-cc -DHAVE_CONFIG_H -I. -I.. -Wall -g -O2 -c \
	-DHAVE_CONFIG_H \
	-o ~/Repos/euf/tests/regexec_new.bc \
	src/regexec.c

	cd -

	/usr/bin/goto-cc -I. -DCBMC \
		tests/regexec_driver.c \
		tests/regexec_old.bc tests/regexec_new.bc \
	-o main

	# Run verification
	# http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html
	# --function-pointer-restrictions-file tests/regexec_restrict.txt
	cbmc --function main --trace --z3 --drop-unused-functions --unwind 4 ./main
else
	/usr/bin/gcc -DHAVE_CONFIG_H -I. -I/usr/local/include -Wall -g -O2 -c -E \
	-o ~/Repos/euf/tests/regexec_old.c \
	regexec.c
	
	# Remove the _old suffixes
	git checkout regexec.c

	git checkout 1bd71be9437db6ede501fc88102961423c1ab74c
	
	/usr/bin/gcc -DHAVE_CONFIG_H -I. -I.. -Wall -g -O2 -c -E \
	-o ~/Repos/euf/tests/regexec_new.c \
	src/regexec.c

	cd -
	
	# Expand preprocessor directives in driver and cat togheter all three files
	/usr/bin/gcc -I tests tests/smack_driver.c -c -E -o ./tests/smack_driver_E.c
	cat tests/regexec_new.c tests/regexec_old.c tests/smack_driver_E.c > mnt/smack_driver.c

	./scripts/smack.sh -f mnt/smack_driver.c /mnt/smack_driver.c --no-verify -bpl /mnt/smack_driver.bpl
fi

cd ~/Repos/oniguruma && git checkout $BRANCH && cd -
