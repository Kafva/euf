#!/usr/bin/env bash
# Should be executed with the repo in question as cwd
[[  -z "$SUFFIX" || -z "$RENAME_YML" || -z "$VERBOSE" ]] && 
	die "Missing environment variable(s)"

# Replace all occurences of the top level identifiers in the project
# To avoid FPs we only replace occurences of the <name> not enclosed by:
c_chars="[^_0-9a-zA-Z]"

sed -nE "s/- QualifiedName: (.*)/\1/p" "$RENAME_YML" > /tmp/rename.txt

worker_job(){
	while read -r old_name; do
		# The expressions matches several occurences per line of the
		# old name enclosed by either a character that is not a allowed
		# as a part of an identifer or start-of-line/end-of-line
		sed -E -i'' \
			-e "s/(${c_chars}|^)(${old_name})(${c_chars}|$)/\1\2${SUFFIX}\3/g" \
			"$1"

		# Only read the list of global names from the YML
	done < /tmp/rename.txt
}

WORKER_CNT=$((`nproc` - 1))
files=()

while read -r file; do
	# Skip any none .h / .c files
	echo "$file" | grep -q "\.[hc]$" || continue

	files+=( "$file" )

	# Launch `WORKER_CNT` background jobs to perform replacements
	# (one file per worker) and wait for each to complete
	if [ ${#files[@]} = $WORKER_CNT ]; then

		worker_pids=()

		for i in $(seq 0 $((WORKER_CNT-1))); do
			$VERBOSE && echo "Renaming all global symbols in '${files[$i]}'" >&2

			worker_job "${files[$i]}" &
			worker_pids+=( $! )
		done

		for i in $(seq $WORKER_CNT); do
			wait ${worker_pids[$i]}
		done

		files=()
	fi
	

done < <(git ls-tree -r HEAD --name-only)
