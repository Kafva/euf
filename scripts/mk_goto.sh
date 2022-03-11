#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
goto_compile(){
	$SETX && set -x

	# FIXME: Temporary solution
	#find ~/.cache/euf -name "matrix-*" |xargs -I{} bash -c 'cp ~/Repos/matrix/Makefile {}'

	cd $DEPENDENCY_DIR
	make clean 2> /dev/null

	[[  -f "configure.ac" || -f "configure.in" ]] &&
		autoreconf -fi || 
		echo "!> Missing autoconf script" >&2 

	[ -f "configure" ] &&
		./configure CC=goto-cc LD=goto-cc --host none-none-none ||
		echo "!> Missing ./configure" >&2

	[ -f "Makefile" ] &&
		make CC=goto-cc LD=goto-cc -j$((`nproc` - 1)) ||
		echo "!> Missing Makefile" >&2
	
	# Print the path to the library
	find $DEPENDENCY_DIR -name "$DEPLIB_NAME" | head -n1

	$SETX && set +x
	return 0
}

# Compile the given dependency as a goto-bin static library and echo out
# its path
[[  -z "$DEPENDENCY_DIR" || -z "$SETX" || -z "$FORCE_RECOMPILE" || 
	-z "$DEPLIB_NAME" ]] && die "Missing environment variable(s)"

if $FORCE_RECOMPILE; then 
	goto_compile
fi

# Always recompile if at least one object file is an ELF file
# goto-bin files are recorded as 'data'
if $(find -name "*.o" | xargs -I{} file -b {} | sort -u | grep -q ELF); then
	goto_compile
fi

if $(find $DEPENDENCY_DIR -name "$(basename $DEPLIB_NAME)" &> /dev/null); then
	printf "!> [$(basename $DEPENDENCY_DIR)]: Found pre-existing library: $DEPLIB_NAME -- Skipping goto-bin compilation\n" >&2

	# Print the path to the dependency
	find $DEPENDENCY_DIR -name "$DEPLIB_NAME" | head -n1
else
	goto_compile
fi



