#!/usr/bin/env bash
randname(){
	local chars="abcdefghijklnompqrstuvhijklmnop0123456789"
	local out idx
	for _ in $(seq 1 10); do
		idx=$((RANDOM % ${#chars}))
		out="$out${chars:$idx:1}"
	done
	printf "$out\n"
}

idx=0
cd ~/.cache/euf/libexpat-bbdfcfef

while :; do

	~/Repos/euf/euf.py --config ~/Repos/euf/configs/expat.json
	cp -r ~/.cache/euf/libexpat-bbdfcfef/expat ~/.cache/euf/"$(randname)_$idx"
	git checkout .
	git stash clear

	sleep 5
	idx=$((idx + 1))
done
