#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) [-hV] [-n COMMIT_NEW] [-c COMMIT_CURRENT] [-d DEPENDENCY] <project>"
helpStr=""
VIEW=false

while getopts ":hn:c:d:V" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		n) NEW_COMMIT=$OPTARG ;;
		c) CURRENT_COMMIT=$OPTARG ;;
		d) DEPENDENCY_DIR=$OPTARG ;;
		V) VIEW=true ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

[ -z "$1" ] 			&& die "$usage"
[ -z "$NEW_COMMIT" ] 		&& die "$usage"  
[ -z "$CURRENT_COMMIT" ] 	&& die "$usage"  
[ -d "$DEPENDENCY_DIR" ] 	|| die "$usage"  

PROJECT=$1
LC_ALL=C

# Note that we switch to the new commit and perform a diff agianst
# the current state to see changes from the correct perspective
cd $DEPENDENCY_DIR
git checkout $NEW_COMMIT &>/dev/null || die "Failed to checkout current commit"

if $VIEW; then
	git diff --ignore-space-change --ignore-blank-lines --function-context \
		--diff-filter M $CURRENT_COMMIT -- "***.c" "***.h" | \
			tr -dc '\0-\177' | bat
else
	# We only consider modifications (M) to source files
	# 	- We ignore changes to comments '//' 
	#	- We ignore non-printable characters
	#	- Multi line comments haft to be parsed away later
	# We remove the @@ context markers
	git diff --ignore-space-change --ignore-blank-lines --function-context \
		--diff-filter M $CURRENT_COMMIT -- "***.c" "***.h" | \
			sed -E '/^[[:space:]]*[+-]+\/\//d' | \
			tr -dc '\0-\177' | \
			sed -E 's/@@\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+@@//' \
			> /tmp/$CURRENT_COMMIT.diff
fi

git checkout master &>/dev/null || git checkout main
cd - &> /dev/null
