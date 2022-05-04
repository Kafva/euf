#!/usr/bin/env bash
: '''
  * Run X random cases for each project

  * Grep out the subset of equivalent (`SUCCESS`) (TN|FN) cases, 
    there should be a major overlap in what functions appear

  * Grep out the subset of influential (`FAILURE`) (TP|FP) cases, 
    there should be a major overlap in what functions appear

  * Interrogate each function individually to determine if the result is trustworthy
    - Record in a CSV:
       - function_name;dependency;results;trusted
    - "results" should hold all recorded results for this function
    - "trusted" should be set as True, True(unwind) False or Inconclusive
    - "description" should motivate the trusted column"s value (seperate
      markdown doc, with pictures)
'''
RESULT_DIR=$PWD/results

bat_opts=(--language=csv --paging=never --color=always 
  --style=plain  --theme=ansi
)

get_cases(){
  local case_name=$1
  local identity=$2
  printf "=> \033[34m$case_name\033[0m (identity: \033[34m$identity\033[0m)\n"
  #awk -F';' '/False;SUCCESS/{print $1,$3}' results/${case_name}_*/cbmc.csv

  #== Real comparisons ==#
  echo "========= Equivalent (SUCCESS) ========="
  awk -F';' "/$identity;SUCCESS/{print \$1,\$3}" results/${case_name}_*/cbmc.csv |
    sort -u

  echo "======== Influential (FAILURE) =========="
  awk -F';' "/$identity;FAILURE/{print \$1,\$3}" results/${case_name}_*/cbmc.csv |
    sort -u

}


get_cases libexpat True
get_cases libonig  True
get_cases libusb-1.0 True

echo -e "\n≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈≈\n"

get_cases libexpat False
get_cases libonig  False
get_cases libusb-1.0 False


