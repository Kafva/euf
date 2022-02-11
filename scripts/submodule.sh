#!/bin/sh

cd $1

git submodule update --init --recursive
current_commit=$(git submodule | sed -E 's/^(\s*|-)([a-z0-9]{40}).*/\2/p')

