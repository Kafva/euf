#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <.diff>"
helpStr=""
MAIN=src/main.c
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


mkdir -p ir
make clean

#----------------------------#
clang -I include -S -emit-llvm src/$DEP.c -o ir/$DEP.ll.old

# Patch source and recompile
patch -p1 < $diff_file

clang -I include -S -emit-llvm src/$DEP.c -o ir/$DEP.ll.new

# Revert patch
patch -p1 -R < $diff_file

# llvm-diff --color strcpy.ll.new strcpy.ll.old
diff --color=always -y ir/$DEP.ll.old ir/$DEP.ll.new | less -r




