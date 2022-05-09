#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
[ -z "$1" ] && die "$0 <pid>"

NICE_LEVEL=0

process_id=$1
echo renice $NICE_LEVEL $process_id
sudo renice $NICE_LEVEL $process_id

recurse(){
  children=$(cat /proc/$1/task/$1/children)
  if [ -n "$children" ]; then
     for child in $children; do
        echo renice $NICE_LEVEL $child
        sudo renice $NICE_LEVEL $child
        recurse $child
     done
  else
     return
  fi
}

recurse $process_id

