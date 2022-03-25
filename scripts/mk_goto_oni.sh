#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
goto_compile(){
	# Note that the compilation 'fails' for oniguruma but libonig.a is still
	# produced and usable (not really)
	$SETX && set -x

	cd $DEP_DIR_EUF
	make clean
	git clean -df --exclude=compile_commands.json

	#[[  -f "configure.ac" || -f "configure.in" ]] &&
	#	autoreconf -fi || 
	#	echo "!> Missing autoconf script" >&2 

	[ -f "configure" ] &&
		./configure CC=goto-cc --host none-none-none ||
		echo "!> Missing ./configure" >&2

	[ -f "Makefile" ] &&
		make CC=goto-cc -j$PROCS ||
		echo "!> Missing Makefile" >&2
	
	# Print the path to the library
	find $DEP_DIR_EUF -name "$DEPLIB_NAME" | head -n1

	$SETX && set +x
	return 0
}

PROCS=$((`nproc` - 1))

# Compile the given dependency as a goto-bin static library and echo out
# its path
[[  -z "$DEP_DIR_EUF" || -z "$SETX" || -z "$FORCE_RECOMPILE" || 
	-z "$DEPLIB_NAME" ]] && die "Missing environment variable(s)"

if $FORCE_RECOMPILE; then 
	goto_compile
	exit $?
fi

# Always recompile if at least one object file is an ELF file
# goto-bin files are recorded as 'data'
if $(find -name "*.o" | xargs -I{} file -b {} | sort -u | grep -q ELF); then
	goto_compile
	exit $?
fi

DEPLIB_PATH=$(find $DEP_DIR_EUF -name "$(basename $DEPLIB_NAME)" 2>/dev/null | head -n1)

if [ -n "$DEPLIB_PATH" ]; then
	printf "!> [$(basename $DEP_DIR_EUF)]: Found pre-existing library: $DEPLIB_NAME -- Skipping goto-bin compilation\n" >&2

	# Print the path to the dependency
	printf "$DEPLIB_PATH"
else
	goto_compile
fi



