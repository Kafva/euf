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

[ -z "$1" ] && die "$usage"
[ -z "$NEW_COMMIT" ] && die "$usage"  
[ -z "$CURRENT_COMMIT" ] && die "$usage"  
[ -d "$DEPENDENCY_DIR" ] || die "$usage"  

PROJECT=$1

#----------------------------#
# ./scripts/euf.sh -c 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n 29754fab4e3e332d9d19d68d55d760be48a44c1b -d ../jq/modules/oniguruma ../jq
# ./scripts/euf.sh -c 6c51de92d73ee1e6b54257947ca076b3945d41bd -n 5dc3be2af4e436cd5236157e89ff04b43c71f613 -d ../sck ..
# ./scripts/euf.sh -c 1fe1a3f7a52d8d86df6f59f2a09c63c849934bce -n eb780c3c7294d4ef1db1cb8dcebbfe274e624d99 -d ../DBMS ..

# 1. Get the diff between the current and new versions
# 	- Extract the names of the affected functions
cd $DEPENDENCY_DIR
git checkout $CURRENT_COMMIT

# The function-context option ensures that the enclosing function name
# is always printed first in the context @@ of each change

# We only consider modifications (M) to source files
git diff --ignore-space-change --ignore-blank-lines --function-context \
	--diff-filter M $NEW_COMMIT -- "***.c" "***.h" "***.cpp" "***.hpp" \
	> /tmp/$NEW_COMMIT.diff



cd -
