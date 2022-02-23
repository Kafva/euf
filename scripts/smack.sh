#!/usr/bin/env bash
usage="usage: $(basename $0) [-f mount-file] <cmds>"
die(){ echo -e "$1" >&2 ; exit 1; }

while getopts ":hf:" opt; do
	case $opt in
		h) die "$usage\n-----------\n$helpStr" ;;
		f) MNT_FILE=$OPTARG ;;
		*) die "$usage" ;;
	esac
done

shift $(($OPTIND - 1))

#----------------------------#
# The docker build fails if we have smack as a submodule in ./euf
[ -d ../smack ] || die "Not found ../smack"
docker images --format "{{.Repository}}" | grep -q "smack" ||
	docker build --rm --tag=smack ../smack

if [ -n "$MNT_FILE" ]; then
	#docker run --rm -v $PWD/$MNT_FILE:/$(basename $MNT_FILE) smack $@
	cp $MNT_FILE $PWD/mnt
	docker run --rm -v $PWD/mnt:/mnt smack $@
else
	docker run --rm smack $1
fi

