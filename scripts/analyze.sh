#!/usr/bin/env bash
: '''
We need a viewer script:
  - Read all False;SUCCESS|FAILURE rows from the result
  - Open a split with the diff of the function and the harness
  - Record (TN|FN|TP|FP) in a seperate csv on the form

Manual labeling file:


Of intrest: 
  Reduction % for each case
  SUCCESS (ID) harnesses for each case

'''
