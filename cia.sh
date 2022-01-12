#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""
MAIN=main.c
DEP=strcpy.c

while getopts ":h" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

[ -z "$1" ] && die "$usage"


#----------------------------#
clang -S -emit-llvm $DEP -o old_${DEP%%.c}.ll

# Patch source and recompile

clang -S -emit-llvm $DEP -o new_${DEP%%.c}.ll
