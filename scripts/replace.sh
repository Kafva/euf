#!/usr/bin/env bash
# Replace all occurrences of the top level identifiers in the project
# Should be executed with the repo in question as cwd
[[  -z "$SUFFIX" || -z "$RENAME_YML" || -z "$VERBOSE" ]] && 
	die "Missing environment variable(s)"


worker_job(){
	# Remove all comments from the source file before any processing
	# This operation does not expand macros (but it can fck up some other preproccessor directives)
	#~/Repos/euf/scripts/ccomments.sed "$1" > "$tmp_file"
	# gcc -fpreprocessed -dD -P -E "$1" > "$tmp_file"

	# Remove the license header (if any from the file)
	# (Very hacky)
	local tmp_file="/tmp/$(basename ${1})_$RANDOM"

	local start=$(grep -E -m1 -n "^\s*(/\*)"  "$1" |awk -F: '{print $1}')
	local end=$(grep -E -m1 -n "^\s*(\*/)"    "$1" |awk -F: '{print $1}')

	sed "${start},${end}d" "$1" > "$tmp_file"

	local old_name
	while read -r old_name; do
		# Note that we exclude all lines starting with '#include' to avoid
		# path names being renamed
		# We also skip '//' single line comments

		# To avoid replacements of partial matches in an identifier we only 
		# replace occurrences of the <name> NOT enclosed by ${DELIM}

		# We can get issues when matches inside strings are replaced...

		# The expression matches several occurrences per line of the
		# old name enclosed by either a character that is not a allowed
		# as a part of an identifier or start-of-line/end-of-line
		#
		# We only replace the enclosements which are followed by a "
		# preceded by a "
		# or neither
		sed -E -i'' \
			-e '/^\s*(#\s*include|\/\/)/!'"s/(${DELIM}|^)(${old_name})(${DELIM}|$)/\1\2${SUFFIX}\3/g" \
			"$tmp_file"

		# Only read the list of global names from the YML
	done < $RENAME_TXT

	cp "$tmp_file" "$1"
}


RENAME_TXT=/tmp/rename.txt
TO_RENAME_TXT=/tmp/to_rename.txt

# Every word that we replace needs to be enclosed by some character NOT in this set (or have nothing around it)
# Furthermore, there cannot be a "' before or after the symbol
DELIM="[^_0-9a-zA-Z]"

WORKER_CNT=$((`nproc` - 1))
files=()

# For testing
if [ -f "$1" ]; then
	worker_job "$1"
	exit 0
fi

# To disperse the work evenly we order the input files in descending order
# of line numbers, all threads will then have a big file to work on
# in the same iteration. Also skip any none .c/.h files
git ls-tree -r HEAD --name-only | xargs -I {} wc -l {} | 
	sort -n -k1 | awk '{print $2}' | grep "\.[hc]$" > $TO_RENAME_TXT

TOTAL=$(wc -l $TO_RENAME_TXT | awk '{print $1}')
cnt=0

# Extract the names of all globals to a newline-separated file
sed -nE "s/- QualifiedName: (.*)/\1/p" "$RENAME_YML" > $RENAME_TXT

echo "!> Starting $(basename $0) at $PWD"

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
