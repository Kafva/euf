[ "$1" = off ] && sed -E -i'.rm' 's@^(\s*)__CPROVER@\1// __CPROVER@g' src/*
[ "$1" = on ]  && sed -E -i'.rm' 's@^(\s*)// __CPROVER@\1__CPROVER@g' src/*

rm -f src/*.rm
