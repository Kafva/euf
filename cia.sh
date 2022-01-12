#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""
MAIN=main.c

while getopts ":h" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

[ -z "$1" ] && die "$usage"

#----------------------------#
ll_name=${1%%.c}.ll

clang -S -emit-llvm $1 -o old_$ll_name

# Patch source and recompile

clang -S -emit-llvm $1 -o new_$ll_name
