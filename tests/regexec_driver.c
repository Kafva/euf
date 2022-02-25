#include "cprover_builtin_headers.h"
#include <stdlib.h>

extern int nondet_int();
extern void* nondet_ptr();

// Fictional example of a function to check
//	extern int onig_number_of_captures(struct regex_t* reg)

int main(int argc, char* argv[]){

	void* ptr1 = nondet_ptr(); 	
	void* ptr2 = nondet_ptr(); 	
	__CPROVER_assume( ptr1 != 0 && ptr2 != 0 );
	__CPROVER_assume( ptr1 == ptr2 );
	
	// http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html
	

	//struct regext_t* ptr1 = (struct regex_t*)malloc(100);
	//ptr1->num_mem = 4;
	//struct regext_t* ptr2 = (struct regex_t*)malloc(100);
	//ptr2->num_mem = 4;

	int res1 = onig_number_of_captures_old(ptr1);
	int res2 = onig_number_of_captures(ptr2);
	
	__CPROVER_assert( res1 == res2, "Same result");

	//free(ptr1);
	//free(ptr2);
	return 0;
}


