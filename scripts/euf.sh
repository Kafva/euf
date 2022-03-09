#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) [-hV] [-n NEW_COMMIT] [-f dep-file] [-o OLD_COMMIT] [-d DEPENDENCY] <project>"
helpStr=""
VIEW=false
NEW_MODE=false

while getopts ":hn:o:d:Vf:N" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		n) NEW_COMMIT=$OPTARG ;;
		o) OLD_COMMIT=$OPTARG ;;
		d) DEPENDENCY_DIR=$OPTARG ;;
		V) VIEW=true ;;
		f) DEP_ONLY=$OPTARG ;;
		N) NEW_MODE=true ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

[ -z "$1" ] 			&& die "$usage"
[ -z "$NEW_COMMIT" ] 		&& die "$usage"  
[ -z "$OLD_COMMIT" ] 		&& die "$usage"  
[ -d "$DEPENDENCY_DIR" ] 	|| die "$usage"  

PROJECT=$1
LC_ALL=C

# Note that we switch to the new commit and perform a diff agianst
# the current state to see changes from the correct perspective
cd $DEPENDENCY_DIR
git checkout $NEW_COMMIT &>/dev/null || die "Failed to checkout new commit"

if $NEW_MODE; then
	git diff --ignore-space-change --ignore-blank-lines \
		~/.cache/euf/$(basename $DEPENDENCY_DIR)-${NEW_COMMIT:0:8}/src/$DEP_ONLY \
		~/.cache/euf/$(basename $DEPENDENCY_DIR)-${OLD_COMMIT:0:8}/$DEP_ONLY
fi

if $VIEW; then
	# Show 3000 lines of context for every change
	git diff --ignore-space-change --ignore-blank-lines -U3000 \
		--diff-filter MR $OLD_COMMIT -- "***.c" "***.h" | \
			tr -dc '\0-\177'
elif [ -n "$DEP_ONLY" ]; then
	git diff --ignore-space-change --ignore-blank-lines -U3000 \
		--diff-filter MR $OLD_COMMIT -- "**$DEP_ONLY" | \
			tr -dc '\0-\177'
else
	# We only consider modifications (M) and renamed (R) source files
	# 	- We ignore changes to comments '//' 
	#	- We ignore non-printable characters
	#	- Multi line comments haft to be parsed away later
	# We remove the @@ context markers
	git diff --ignore-space-change --ignore-blank-lines --function-context \
		--diff-filter MR $OLD_COMMIT -- "***.c" "***.h" | \
			sed -E '/^[[:space:]]*[+-]+\/\//d' | \
			tr -dc '\0-\177' | \
			sed -E 's/@@\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+[-+]*[[:digit:]]+,[-+]*[[:digit:]]+\s+@@//' \
			> /tmp/$OLD_COMMIT.diff
fi

git checkout master &>/dev/null || git checkout main
cd - &> /dev/null
