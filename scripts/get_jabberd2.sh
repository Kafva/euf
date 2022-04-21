#!/usr/bin/env bash
# Hacky way of building the compilation database for jabberd2
# Using `autoreconf` with the git version does not work but building
# through the release source does...

#rm -rf ~/Repos/{jabberd2,jabberd-2.7.0}
rm -rf /tmp/{jabberd2,jabberd-2.7.0}

curl -L https://github.com/jabberd2/jabberd2/releases/download/jabberd-2.7.0/jabberd-2.7.0.tar.gz | 
	tar xzf - -C ~/Repos

git clone -b jabberd-2.7.0 https://github.com/jabberd2/jabberd2.git /tmp/jabberd2

cd /tmp/jabberd2 && git switch -c main
mv .git ~/Repos/jabberd-2.7.0

cd ~/Repos/jabberd-2.7.0
git checkout util/{misc.c,misc.h,pqueue.c,pqueue.h}
./configure &&
bear -- make -j$((`nproc` - 1))
