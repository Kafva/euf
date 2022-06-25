#!/usr/bin/env bash
SECONDS_RUNTIME=runtime.csv

: '''
To get an approximation of the average runtime for a trial we
sum up all verification times for each case. To make the comparsion fair
we model every PREV_TIMEOUT as having a runtime of 4 minutes
'''

write_csv(){
  local tmpfile="/tmp/runtimes"
  echo "case;runtime" > $SECONDS_RUNTIME
  for trial in .results/13/*/cbmc.csv; do
    local case_name=$(basename $(dirname $trial))

    rg PREV_TIMEOUT $trial | sed 's/^.*$/0:04:00.000000/' > $tmpfile
    sed -E '/PREV_TIMEOUT|runtime/d' $trial | awk -F';' '{print $4}'  | 
      sed -E '/^\s*$/d' >> $tmpfile

python3 << EOF
from dateutil import parser
total_seconds=0
with open("$tmpfile", mode='r', encoding='utf8') as f:
  for runtime in f.readlines():
    t = parser.parse(runtime)
    total_seconds += t.minute*60 + t.second
with open("$SECONDS_RUNTIME", mode='a', encoding='utf8') as f:
  f.write(f"$case_name;{total_seconds}\\n")
EOF

  done
}

get_stats(){
python3 << EOF
from statistics import mean, stdev
values = []
def pretty(sec):
  return f"{int(int(sec)/60)}.{int(sec%60)}"

with open("$SECONDS_RUNTIME", mode='r', encoding='utf8') as f:
  for line in f.readlines()[1:]:
    if line.split(';')[0].startswith("$1") or "$1" == "":
      values.append(int(line.split(';')[1]))
    

average_value = pretty(round(mean(values),3))
stdev_value = pretty(round(stdev(values),3))
print(f"($1) Average runtime: {average_value} (±{stdev_value})"
)
EOF
}

#write_csv
get_stats libonig
get_stats libexpat
get_stats libusb
get_stats
