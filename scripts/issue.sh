#!/usr/bin/env bash
[ -d /tmp/libexpat ] ||
	git clone git@github.com:libexpat/libexpat.git /tmp

cd /tmp/libexpat/expat && 
	./configure CC=goto-cc --host none-none-none && 
	make -j$((`nproc` - 1))

cat << EOF > driver.c
#include "lib/expat.h"

int main(){
	XML_Error code = 0;
	XML_LChar out = XML_ErrorString(code);
	assert( out == 0 );
	return 0;
}
EOF

cbmc driver.c .libs/libexpat.a --list-goto-functions
