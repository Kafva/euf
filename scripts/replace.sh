#!/usr/bin/env bash
# Should be executed with the repo in question as cwd
[[  -z "$SUFFIX" || -z "$RENAME_YML" || -z "$VERBOSE" ]] && 
	die "Missing environment variable(s)"

# Replace all occurences of the top level identifiers in the project
# To avoid FPs we only replace occurences of the <name> not enclosed
# by [-_0-9a-zA-Z]
git ls-tree -r HEAD --name-only > /tmp/git-tree

while read -r line; do
	old_name=$(echo $line | sed -nE "s/- QualifiedName: (.*)/\1/p")
	if [ -n "$old_name" ]; then
		$VERBOSE && echo "Renaming all occurences of '$old_name'" >&2

		while read -r file; do
			# Skip any none .h / .c files
			echo $file | grep -q "\.[hc]$" || continue

			sed -E -i'' "s/(.*[^-_0-9a-zA-Z])(${old_name})([^-_0-9a-zA-Z].*)/\1\2${SUFFIX}\3/" "$file"
		done < /tmp/git-tree
	fi
	
done < "$RENAME_YML"

