#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
usage="usage: $(basename $0) <...>"
helpStr=""
goto_compile(){
	cd "$1"

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
		make CC=goto-cc -j$PROCS	|| return -1
	else
		echo "!> Missing Makefile" >&2
	fi

	# Print the path to the library
	find "$1" -name "$DEPLIB_NAME" | head -n1

	return 0
}

[[ -z "$DEP_DIR_NEW" || -z "$SUFFIX"  || -z "$DEP_DIR_OLD" ]] && 
	die "Missing enviroment variable(s)"


# 1. Compile the new and old version of the library
goto_compile $DEP_DIR_OLD

GOTO_DIR=/tmp/goto
mkdir -p $GOTO_DIR

for objfile in $(jq -rM '.[].output' compile_commands.json); do
	[ -f "$objfile" ] || continue
	decompiled=$GOTO_DIR/$(basename ${objfile%%.o}_E.c)
	re_compiled=$GOTO_DIR/$(basename ${objfile%%.o}.gb)
	goto-instrument --dump-c $objfile | sed '1d' > $decompiled

	# ... Add suffixes and remove static specifiers ...

	# This does not work
	goto-cc $decompiled -o $re_compiled
done


ar rcs $GOTO_DIR/*.gb -o $GOTO_DIR/libexpat.a


#goto_compile $DEP_DIR_NEW


# DEP_DIR_NEW=~/.cache/euf/libexpat-bbdfcfef/expat DEP_DIR_OLD=~/.cache/euf/libexpat-c16300f0/expat SUFFIX=_old ./scripts/goto-patch.sh


# 2. Dump the simplified C-code for each object file in the old library
#		* Remove static specifiers
# 	* Run clang-suffix on all of the decompiled source files, indivudally (everything should be 
# 	self contained so we only need a stub compile_commands.json)
#
# 3. Re-link all of the decompiled source files into a `lib_old.a` link the driver agianst both versions
#			Or maybe just link agianst the specific object file that is needed
