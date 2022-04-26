#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
RUNNER=${RUNNER:=runner}
CONTEXT_LINES=${CONTEXT_LINES:=200}

[ -z "$1" ] && die "No name provided"

tmp1=$(mktemp)
tmp2=$(mktemp)
cbmc --show-goto-functions $RUNNER | grep -m1 -A$CONTEXT_LINES "^$1 " > $tmp1
cbmc --show-goto-functions $RUNNER | grep -m1 -A$CONTEXT_LINES "^${1}_old" > ${tmp2}


get_func_body(){
  while read -r line ; do
    echo "$line"
    echo "$line" | 
      grep -q END_FUNCTION && break
  done < $1

}

out=/tmp/$1.gb
out_old=/tmp/${1}_old.gb

get_func_body $tmp1 > $out
get_func_body $tmp2 > $out_old

git difftool --no-index $out $out_old
