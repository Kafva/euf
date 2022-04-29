#!/usr/bin/env bash
: '''
We need a viewer script:
  - Read all False;SUCCESS|FAILURE rows from the result
  - Open a split with the diff of the function and the harness
  - Record (TN|FN|TP|FP) in a seperate csv on the form

Manual labeling file:

Of intrest: 
  Reduction % for each case
  SUCCESS (ID) harnesses % for each case

'''

CASE=${CASE:=results/libusb-1.0_4a55_500c}
COMMIT_OLD=$(echo $CASE|sed -E 's/.*_(.{4})_.*/\1/' )
COMMIT_NEW=$(echo $CASE|sed -E 's/.*_(.{4})_(.{4}).*/\2/' )

while read -r line; do

  func_name=$(echo $line | awk -F';' '{print $1}')
  identity=$(echo $line | awk -F';' '{print $2}')
  result=$(echo $line | awk -F';' '{print $3}')
  driver=$(echo $line | awk -F';' '{print $5}')
  
  # Retrive the origin of the change from the first
  # line of the harness
  sed -nE '1s@.*a/(.*) -> .*@\1@p' $driver

  #(sleep 2; git difftool --no-index  )
  #tmux split-window -h -p 50 \;
  #  send-keys nvim $driver \;
  echo $line

done < <(sed '1d' $CASE/cbmc.csv)


