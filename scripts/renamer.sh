#!/usr/bin/env bash


# ./clang/tools/clang-rename/ClangRename.cpp
#
# `clang-rename` renames symbols in the current .c file AND all headers were the symbol
# is referenced. This causes issues when other .c files reference the old name of a
# symbol that has been renamed in the headers
#
# To circumvent this we can: 
#   1. Individually rename the symbols in each .c file
# If we patched the clang-rename program to not rename headers we could run these
# processes in parallel


# all source files at once and not one by one
# Using --force will suppress all errors but still apply changes
#
# The documentation says that it only works for single TUs but it is possible to replace
# in multiple files at the same time
# 

cd ~/.cache/euf/oniguruma-65a9b1aa

git checkout .

for tu in $(find . -name "*.c"); do
	echo "$tu" | grep -q ccls-cache && continue

	echo "Renaming $tu..."
	clang-rename --force --input /tmp/rename.yml -i $tu  -- \
		-DHAVE_CONFIG_H -I. -I/usr/local/include -g -O2 -c -fPIC || exit -1

	# We don't do git checkout *.h directly since the index could
	# have none-existent files (e.g. config.h in oniguruma)
	for hdr in $(find . -type f \( -name "*.h" -o -name "*.inc" \)); do
		echo "$hdr" | grep -q ccls-cache && continue
		git checkout "$hdr"
	done
done

# Rename the headers last
for hdr in $(find . -type f \( -name "*.h" -o -name "*.inc" \)); do
	echo "$hdr" | grep -q ccls-cache && continue
	git checkout "$hdr"
done

