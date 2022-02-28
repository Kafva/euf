#include "cprover_builtin_headers.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

extern int nondet_int();

int main(int argc, char* argv[]){

	int k1 = nondet_int();
	int k2 = nondet_int();
	__CPROVER_assume(k1 == k2);

	int res1 = get_nearest_even_old(k1);
	int res2 = get_nearest_even(k2);
	__CPROVER_assert(res1 == res2, "Equivalent behaviour"); 

	return 0;
}

