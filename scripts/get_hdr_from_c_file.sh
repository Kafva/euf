#!/usr/bin/env bash
: '''
Some files like regparse.c, regcomp.c in oniguruma and xmlparse.c in libexpat
contain struct and type definitions which we need inside of drivers.

This script is meant to partially automate the creation of custom headers
that resolve this issue
'''
die(){ echo -e "$1" >&2 ; exit 1; }

target_file="$1"
output_file=your_header.h

[ -f "$target_file" ] || die "Not a file"

multi_line=
in_struct=

rm -f $output_file

idx=0
while read -r line; do

  if [[ -n "$multi_line" || -n "$(echo $line|grep -o '^#define')" ]]; then

    echo "$line" >> "$output_file"
    echo "$line" | grep -q '\\$' && multi_line=true || multi_line=

  elif [[ -n "$in_struct" || -n "$(echo $line|grep -o '^enum\|typedef\|struct')" ]]; then

    echo "$line" >> "$output_file"
    echo "$line" | grep -q "^}" && in_struct="" || in_struct=true

  elif $(echo "$line"|grep -q '^#if\|#ifdef\|#endif'); then
    echo "$line" >> "$output_file"
  fi

  idx=$((idx+1))
  #[ $idx = 2000 ]&&break

done < "$target_file"


