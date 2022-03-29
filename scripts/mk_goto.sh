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

	cd $DEP_DIR_EUF

	# make clean && ./configure CC=goto-cc --host none-none-none && make CC=goto-cc -j9
	make clean
	git clean -df --exclude=compile_commands.json

	echo "!> Starting goto-bin compilation: $DEPLIB_NAME" >&2
	
	# This is not the same as running from cli for expat?
	if [ -f "configure" ]; then
		./configure CC=goto-cc --host none-none-none
	else
		echo "!> Missing ./configure" >&2
	fi
		
	if [ -f "Makefile" ]; then
		bash -c "make CC=goto-cc -j$PROCS $CFLAGS"	|| return -1
	else
		echo "!> Missing Makefile" >&2
	fi

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
	printf "\n!> [$(basename $DEP_DIR_EUF)]: Found pre-existing library: $DEPLIB_NAME -- Skipping goto-bin compilation\n" >&2

	# Print the path to the dependency
	printf "$DEPLIB_PATH"
else
	goto_compile
fi



