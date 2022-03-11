#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
[ -d "$1/.git" ] ||  die "$0 <repo>"

cd "$1"
git stash clear
git worktree list | awk '/euf-/{print $1}' | xargs -I{} sh -c "rm -rf {}"
git worktree prune
git branch | sed '/^\*/d' | xargs -I{} sh -c "git branch -D {}"

