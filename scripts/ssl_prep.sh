#!/usr/bin/env bash
# https://github.com/danbev/learning-libcrypto/blob/master/notes/building.md
./config CC=goto-cc no-shared

make -j$((`nproc` - 1)) build_generated
make -j$((`nproc` - 1)) crypto/buildinf.h
make -j$((`nproc` - 1)) apps/progs.h
