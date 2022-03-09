#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#ifdef CBMC
	#include "cprover_builtin_headers.h"
	extern int  nondet_int();
	extern int* nondet_int_pointer();
#endif

#include "oniguruma_new.h"
#include "oniguruma_old.h"

// We test a simple function that has not changed as a basecase
// 	st.c: int new_size(int)

int main(int argc, char* argv[]){
	// - - - Init - - -
	#ifdef CBMC
	// Uninitialised variables are automatically treated as 'nondet' by CBMC
	int size = nondet_int();
	#else
	int size = 10;
	#endif

	int ret_old = new_size_old(size);
	int ret_new = new_size(size);
	
	// - - - Assert - - -
	#ifdef CBMC
	__CPROVER_assert(ret_old == ret_new, "Equivalent behaviour");
	#endif
	
	return 0;
}



