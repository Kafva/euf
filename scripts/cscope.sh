#!/usr/bin/env bash
cd ~/.cache/euf/oniguruma-65a9b1aa
SUFFIX=_old_b026324c6904b2a

# Find any locations that failed to be renamed
while read -r line; do
	old_name=$(echo $line | sed -nE "s/- QualifiedName: (.*)/\1/p")
	if [ -n "$old_name" ]; then
		OUT=$(grep  --include "*.h" --include "*.c" --exclude-dir=.ccls-cache --color=always -Rn "[^-_0-9a-zA-Z]$old_name[^-_0-9a-zA-Z]" . | sed "/.*${old_name}${SUFFIX}.*/d")
		[ -n "$OUT" ] &&
			printf "\033[34m==>\033[0m $old_name \033[34m<==\033[0m\n$OUT\n"
		
	fi
	
done < /tmp/rename.yml
