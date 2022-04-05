while read -r line; do

  if $(echo $line|grep -q ".[ch]$"); then
      echo $line
  fi

done <(git ls-tree -r HEAD --name-only)
