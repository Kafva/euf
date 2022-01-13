#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <.diff>"
helpStr=""
MAIN=main.c
DEP=strcpy

while getopts ":h" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

[ -z "$1" ] && die "$usage"
diff_file=$1


#----------------------------#




clang -S -emit-llvm $DEP.c -o $DEP.ll.old

# Patch source and recompile
patch -p1 < $diff_file

clang -S -emit-llvm $DEP.c -o $DEP.ll.new

# Revert patch
patch -p1 -R < $diff_file

diff --color=always -y $DEP.ll.old $DEP.ll.new | less -r
