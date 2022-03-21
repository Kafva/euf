#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
TO_RENAME_TXT=/tmp/to_rename.txt

cd "$DEPENDENCY_DIR"

git ls-tree -r HEAD --name-only | xargs -I {} wc -l {} | 
	sort -n -k1 | awk '{print $2}' | grep "\.c$" > $TO_RENAME_TXT


while read -r file; do

	sed -E -i'' '/.*_Float(32|64)x?.*/d' "$file"

done < $TO_RENAME_TXT
