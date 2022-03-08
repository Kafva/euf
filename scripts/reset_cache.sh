#!/usr/bin/env bash
[ -n "$SETX" ] && set -x

find ~/.cache/euf -maxdepth 1 -mindepth 1 -type d | 
	xargs -I{} sh -c "cd {} && git checkout ."
find ~/.cache/euf -maxdepth 1 -mindepth 1 -name "*.lock" -type f | 
	xargs -I{} sh -c "rm {}"
