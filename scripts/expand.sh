#!/usr/bin/env bash
while read -r line; do

  if $(echo $line|grep -q "\.[ch]$"); then
      clang -Ilib -E $line -o $line
  fi

done < <(git ls-tree -r HEAD --name-only)
