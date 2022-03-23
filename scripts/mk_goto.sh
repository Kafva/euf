#!/usr/bin/env bash
# Oniguruma cannot be compiled successfully with goto-cc (regardless of if we perform replacements)
# in the old (65...) version.
#	regsyntax.c:65:1: error: reason for conflict at #this: number of members is different
#
# However, all of the object files are available and the archive, libonig.a, which seems to be fully built
# However.... once we link it togheter with the new library we still get a million errors
#
# libcrypto can be compiled successfully with goto-cc but the archive will include some ELF files,
# these have a x86_64 or similar suffix and do not make sense as general goto programs

die(){ echo -e "$1" >&2 ; exit 1; }
goto_compile(){
	# Note that the compilation 'fails' for oniguruma but libonig.a is still
	# produced and usable
	$SETX && set -x

	cd $DEPENDENCY_DIR

	# make clean && ./configure CC=goto-cc --host none-none-none && make CC=goto-cc -j15
	make clean
	git clean -df --exclude=compile_commands.json

	#[[  -f "configure.ac" || -f "configure.in" ]] &&
	#	autoreconf -fi || 
	#	echo "!> Missing autoconf script" >&2 

	echo "Starting goto-bin compilation: $DEPLIB_NAME" >&2
	

	# This is not the same as running from cli for expat?
	[ -f "configure" ] &&
		./configure CC=goto-cc --host none-none-none
	[ -f "configure" ] ||	echo "!> Missing ./configure" >&2

	#[ -f "Makefile" ] &&
	#	make CC=goto-cc -j$PROCS
	#[ -f "Makefile" ] ||	echo "!> Missing Makefile" >&2
	
	# Print the path to the library
	find $DEPENDENCY_DIR -name "$DEPLIB_NAME" | head -n1

	$SETX && set +x
	return 0
}

PROCS=$((`nproc` - 1))

# Compile the given dependency as a goto-bin static library and echo out
# its path
[[  -z "$DEPENDENCY_DIR" || -z "$SETX" || -z "$FORCE_RECOMPILE" || 
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

DEPLIB_PATH=$(find $DEPENDENCY_DIR -name "$(basename $DEPLIB_NAME)" 2>/dev/null | head -n1)

if [ -n "$DEPLIB_PATH" ]; then
	printf "!> [$(basename $DEPENDENCY_DIR)]: Found pre-existing library: $DEPLIB_NAME -- Skipping goto-bin compilation\n" >&2

	# Print the path to the dependency
	printf "$DEPLIB_PATH"
else
	goto_compile
fi



