#!/usr/bin/env bash
# Should be executed with the repo in question as cwd
[[  -z "$SUFFIX" || -z "$RENAME_YML" || -z "$VERBOSE" ]] && 
	die "Missing environment variable(s)"

worker_job(){
	while read -r local old_name; do
		# The expression matches several occurrences per line of the
		# old name enclosed by either a character that is not a allowed
		# as a part of an identifier or start-of-line/end-of-line
		sed -E -i'' \
			-e "s/(${C_CHARS}|^)(${old_name})(${C_CHARS}|$)/\1\2${SUFFIX}\3/g" \
			"$1"

		# Only read the list of global names from the YML
	done < $RENAME_TXT
}

RENAME_TXT=/tmp/rename.txt
TO_RENAME_TXT=/tmp/to_rename.txt

# Replace all occurrences of the top level identifiers in the project
# To avoid FPs we only replace occurrences of the <name> not enclosed by:
C_CHARS="[^_0-9a-zA-Z]"

WORKER_CNT=$((`nproc` - 1))
files=()

# To disperse the work evenly we order the input files in descending order
# of line numbers, all threads will then have a big file to work on
# in the same iteration. Also skip any none .c/.h files
git ls-tree -r HEAD --name-only | xargs -I {} wc -l {} | 
	sort -n -k1 | awk '{print $2}' | grep "\.[hc]$" > $TO_RENAME_TXT

TOTAL=$(wc -l $TO_RENAME_TXT | awk '{print $1}')
cnt=0

# Extract the names of all globals to a newline-seperated file
sed -nE "s/- QualifiedName: (.*)/\1/p" "$RENAME_YML" > $RENAME_TXT

while read -r file; do
	files+=( "$file" )
	cnt=$((cnt + 1))

	# Launch `WORKER_CNT` background jobs to perform replacements
	# (one file per worker) and wait for each to complete
	if [ ${#files[@]} = $WORKER_CNT ]; then

		worker_pids=()

		for i in $(seq 0 $((WORKER_CNT-1))); do
			$VERBOSE && echo "Renaming all global symbols in '${files[$i]}'" >&2

			worker_job "${files[$i]}" &
			worker_pids+=( $! )
		done

		for i in $(seq 0 $((WORKER_CNT-1))); do
			echo "Waiting on worker $i: '${files[$i]}'" >&2
			wait ${worker_pids[$i]}
		done

		echo "=> Completed ($cnt/$TOTAL)" >&2
		files=()
	fi

done < $TO_RENAME_TXT
