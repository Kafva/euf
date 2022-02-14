#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <project>"
helpStr=""

while getopts ":hn:c:d:" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		n) NEW_COMMIT=$OPTARG ;;
		c) CURRENT_COMMIT=$OPTARG ;;
		d) DEPENDENCY_DIR=$OPTARG ;;
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

# Get the diff between the current and new versions
# 	- Extract the names of the affected functions
cd $DEPENDENCY_DIR
git checkout $CURRENT_COMMIT

# Remove non-printable characters from the output

# We only consider modifications (M) to source files
# 	- We ignore changes to comments '//' 
#	- We ignore non-printable characters
#	- Multi line comments haft to be parsed away later
git diff --ignore-space-change --ignore-blank-lines --function-context \
	--diff-filter M $NEW_COMMIT -- "***.c" "***.h" | \
		sed -E '/^[[:space:]]*[+-]+\/\//d' | \
		tr -dc '\0-\177' | \
		sed -E 's/^\s*-//; s/^\s*\+//;' | \
		sed -E 's/@@\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+@@//' \
		> /tmp/$NEW_COMMIT.diff

# For the lexing to work we need to remove the actual +/- indicators
# and the @@ context markers
cd - &> /dev/null
