# https://github.com/danbev/learning-libcrypto/blob/master/notes/building.md
PROCS=$((`nproc` - 1))

cd "$1"

./config CC=goto-cc no-shared

make -j$PROCS build_generated &&
make -j$PROCS crypto/buildinf.h &&
make -j$PROCS apps/progs.h &&
make -j$PROCS libcrypto.a

