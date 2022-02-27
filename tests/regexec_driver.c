#include "cprover_builtin_headers.h"
#include <stdlib.h>

extern int nondet_int();
extern void* nondet_ptr();

// Example of a function to check
//	extern int onig_number_of_captures(regex_t* reg)

int main(int argc, char* argv[]){
	// TODO: onig_region_free is actually a FP (it has not changed)
	void* ptr1 = nondet_ptr(); 	
	void* ptr2 = nondet_ptr(); 	
	__CPROVER_assume( ptr1 == ptr2 );

	int res1 = onig_number_of_captures_old(ptr1);
	int res2 = onig_number_of_captures(ptr2);
	
	__CPROVER_assert( res1 == res2, "Same result");

	return 0;
}


