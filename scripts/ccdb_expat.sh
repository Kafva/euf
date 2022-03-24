#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
[[ -z "$DEP_SOURCE_ROOT_OLD" || -z "$DEP_SOURCE_ROOT_NEW" || 
   -z "$PROJECT_DIR" || -z "$SETX" 
]] && die "Missing enviroment variable(s)"

bear --version | grep -qE "2\.[0-9]+\.[0-9]+" && 
	v2=true ||
	v2=false

$SETX && set -x

PROCS=$((`nproc` - 1))

if ! [ -f "$DEP_SOURCE_ROOT_OLD/compile_commands.json" ]; then
	cd $DEP_SOURCE_ROOT_OLD
	make clean
	git clean -fd
	git checkout .

	# Custom config with dummy entries for _impl.c files (not needed I think)
	#cp ~/Repos/euf/tests/data/compile_expat.json $DEP_SOURCE_ROOT_OLD/compile_commands.json

	./configure

	if $v2; then
		bear make -j$PROCS
	else
		bear -- make -j$PROCS 
	fi
fi

if ! [ -f "$DEP_SOURCE_ROOT_NEW/compile_commands.json" ]; then
	cd $DEP_SOURCE_ROOT_NEW
	make clean
	git clean -fd
	git checkout .

	./configure

	if $v2; then
		bear make -j$PROCS
	else
		bear -- make -j$PROCS 
	fi
fi

if ! [ -f "$PROJECT_DIR/compile_commands.json" ]; then
	cd $PROJECT_DIR

	git submodule update --init --recursive
	autoreconf -fi
	./configure --with-oniguruma=builtin

	$v2 && 
		bear make -j$PROCS || 
		bear -- make -j$PROCS
fi

exit 0

