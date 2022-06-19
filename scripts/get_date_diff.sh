#!/usr/bin/env bash
# Verify the distance between cases in the data set
# The distances are based on the CommitDate and not the AuthorDate.......
die(){ printf "$1\n" >&2 ; exit 1; }
info(){ printf "\033[34m!>\033[0m $1\n" >&2; }
err(){ printf "\033[31m!>\033[0m $1\n" >&2; }
usage="usage: $(basename $0) <...>"
help_msg=""

git-date () {
  : ''' ai = AuthorDate, ci=CommitDate '''
  git show -s --format=%ai -q $1
}
cde () {
  local basepath=$(printf ~/.cache/euf/*-$1*)
  cd "$basepath"
}

run(){
  local fail_cnt=0
  local cnt=0
  for d in .results/13/$1*; do
    [ -d "$d" ] || continue
    local commit_old=$(sed -E 's/.*_([a-z0-9]{4})_.*/\1/' <<< "$d")
    local commit_new=$(sed -E 's/.*_([a-z0-9]{4})$/\1/' <<< "$d") 

    cd ~/Repos/$1 || return
      local old_date=$(git-date $commit_old 2>/dev/null)
      local new_date=$(git-date $commit_new 2>/dev/null)
    cd ~/Repos/euf

    [[ -z "$old_date" || -z "$new_date" ]] && continue

    local seconds_diff=$(( 
      $(date -d "${old_date}" '+%s') - $(date -d "${new_date}" '+%s') 
    ))

    local day_diff=$(( ${seconds_diff##-} / 86400))
    local fmt="($1) $commit_old ($old_date) -> $commit_new ($new_date): $day_diff"
    if [[ $day_diff -gt 15 || $day_diff -lt 5 ]]; then
      err "$fmt"
      fail_cnt=$((fail_cnt+1))
    else
      echo "$fmt"
    fi
    cnt=$((cnt+1))
  done
  info "Fail count: $fail_cnt/$cnt"
}

run libonig
run libexpat
run libusb-1.0


