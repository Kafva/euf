#!/usr/bin/env bash
# Should be executed with the repo in question as cwd
[[  -z "$SUFFIX" || -z "$RENAME_YML" || -z "$VERBOSE" ]] && 
	die "Missing environment variable(s)"

# Replace all occurences of the top level identifiers in the project
# To avoid FPs we only replace occurences of the <name> not enclosed by:
c_chars="[^_0-9a-zA-Z]"

sed -nE "s/- QualifiedName: (.*)/\1/p" "$RENAME_YML" > /tmp/rename.txt

while read -r file; do
	# Skip any none .h / .c files
	echo "$file" | grep -q "\.[hc]$" || continue

	$VERBOSE && echo "Renaming all global symbols in '$file'" >&2

	while read -r old_name; do
		# The expressions matches several occurences per line of the
		# old name enclosed by either a character that is not a allowed
		# as a part of an identifer or start-of-line/end-of-line
		sed -E -i'' \
			-e "s/(${c_chars}|^)(${old_name})(${c_chars}|$)/\1\2${SUFFIX}\3/g" \
			"$file"

		# Only read the list of global names from the YML
	done < /tmp/rename.txt

done < <(git ls-tree -r HEAD --name-only)
