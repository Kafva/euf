#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
binary=${binary:=main}

# Create trace.o
gcc -g -finstrument-functions -ldl -rdynamic trace.c -c

cd ~/Repos/main
  make clean

# Compile the library and append trace.o to it
cd ~/Repos/matrix
  make clean
  make CFLAGS="-finstrument-functions -ldl -rdynamic" libmatrix.a
  ar r libmatrix.a ~/Repos/euf/trace.o

# Compile the main project (linked agianst libmatrix.a)
cd ~/Repos/main
  make CC=gcc CFLAGS="-finstrument-functions -ldl -rdynamic" main

# Run the main project with instrumentation active
TRACE_LOGFILE=/tmp/trace.out ./main
