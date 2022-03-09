#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
exists(){ [ -f $1 ] || die "Missing $1 script" ; }
get_lib(){
	for libdir in $(find "$1" -type d -name ".libs"); do 
		local static_lib=$(find $libdir -name "*.a")

		[ -n "$static_lib" ] && { 
			printf $static_lib
			return 0
		}
	done

	return -1
}

# Compile the given dependency as a goto-bin and echo out the location of
# a static version of the library
[[  -z "$DEPENDENCY_DIR" || -z "$SETX" || -z "$FORCE_RECOMPILE" ]] && die "Missing environment variable(s)"

if ! $FORCE_RECOMPILE; then
	static_lib=$(get_lib $DEPENDENCY_DIR)
	if [ -n "$static_lib" ]; then 
		printf "[$(basename $DEPENDENCY_DIR)]: Found pre-existing library: " >&2
		printf "$static_lib -- Skipping goto-bin compilation\n" >&2

		printf $static_lib
		exit 0
	fi
fi

$SETX && set -x

cd $DEPENDENCY_DIR
make clean 2> /dev/null

[[  -f "configure.ac" || -f "configure.in" ]] || die "Missing autoconf script"
autoreconf -fi

exists "configure"
./configure CC=goto-cc LD=goto-cc --host none-none-none

exists "Makefile"
make -j$((`nproc` - 1))

$SETX && set +x

get_lib $DEPENDENCY_DIR
