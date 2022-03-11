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

mkdep(){
	make clean &> /dev/null
	./config
	if $v2; then
		bear make -j$PROCS
	else
		bear -- make -j$PROCS 
	fi
}

if ! [ -f "$DEP_SOURCE_ROOT_OLD/compile_commands.json" ]; then
	cd $DEP_SOURCE_ROOT_OLD
	mkdep
fi

if ! [ -f "$DEP_SOURCE_ROOT_NEW/compile_commands.json" ]; then
	cd $DEP_SOURCE_ROOT_NEW
	mkdep
fi

if ! [ -f "$PROJECT_DIR/compile_commands.json" ]; then
	cd $PROJECT_DIR
	which apt &> /dev/null && 
		sudo apt install libssl-dev -y

	make clean &> /dev/null
	autoreconf -fi
	./configure --with-openssl
	$v2 && 
		bear make -j$PROCS || 
		bear -- make -j$PROCS
fi

$SETX && set +x
