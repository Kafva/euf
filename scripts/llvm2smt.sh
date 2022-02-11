#!/bin/bash
docker images | grep -q "^llvm2smt" || docker build --rm --tag llvm2smt ./llvm2smt
docker run --rm -v $PWD/$1:/$(basename $1) llvm2smt /$(basename $1)
