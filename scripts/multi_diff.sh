#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }

START=3
DIRCNT=25
OUTFILE=/tmp/expat_diffs
TMPOUT=$(mktemp)
EXCLUDE=(
	libexpat-bbdfcfef  libexpat-c16300f0  libexpat-e07e3947
)

cd ~/.cache/expats
rm -f $OUTFILE

for i in $(seq $START $DIRCNT); do
	for j in $(seq $i $DIRCNT); do
		[ $i = $j ] && continue
		if [[ -d expat$i && -d expat$j ]]; then
			diff --exclude="*.o" -rq expat$i expat$j  | sed -E 's/expat[0-9]+\///g' >> $TMPOUT
		fi
	done
done

sort -u "$TMPOUT" | sed '/ccls-cache/d' > $OUTFILE


awk '{print $2}' $OUTFILE | xargs -I{} wc -l expat$START/{} | sort -n -k1 -r

while read -r line; do
	name=$(echo $line | awk '{print $2}')

	[ $name = "lib/xmltok.c" ] || continue

	for i in $(seq $START $DIRCNT); do
		for j in $(seq $i $DIRCNT); do
			[ $i = $j ] && continue
			printf "\033[34m===============$i $j=================\033[0m\n"
			git --no-pager diff --color=always --no-index expat$i/$name expat$j/$name
		done
	done


done < $OUTFILE


