#!/usr/bin/env bash



for d in $(git diff --name-only); do
	echo "$d" | grep -q "\.h$" && 
		git checkout "$d"
done

for hdr in $(git ls-tree -r HEAD --name-only); do
	echo "$hdr" | grep -q "\.h$" && 
		clang-rename --input /tmp/rename.yml "$hdr"
done


