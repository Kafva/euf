#!/usr/bin/env bash
OUTFILE=runner
WRAPPER=runner.so
UNWIND=1

OLD_PATH=~/Repos/matrix
NEW_PATH=~/.cache/euf/matrix-30b4d516
DRIVER=tests/matrix_map_driver.c

make -C $OLD_PATH clean && make -C $OLD_PATH libmatrix.so
make -C $NEW_PATH clean && make -C $NEW_PATH libmatrixnew.so

# mv $NEW_PATH/libmatrix.so $NEW_PATH/libmatrixnew.so

clang -Wl,-rpath=$OLD_PATH -L$OLD_PATH -lmatrix \
	-Wl,-rpath=$NEW_PATH -L$NEW_PATH -lmatrixnew \
	$DRIVER -o $OUTFILE


#nm $OUTFILE
#echo "========================"
#nm $OLD_PATH/libmatrix.so
#echo "========================"
#nm $OUTFILE
#nm $NEW_PATH/libmatrixnew.so
./$OUTFILE
