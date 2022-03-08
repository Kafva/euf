#include "smack.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

extern int nondet_int();

int get_nearest_even_old(int k);
int get_nearest_even(int k);


int main(int argc, char* argv[]){

	int k1 = __VERIFIER_nondet_int();
	int k2 = __VERIFIER_nondet_int();
	__VERIFIER_assume(k1 == k2);

	int res1 = get_nearest_even_old(k1);
	int res2 = get_nearest_even(k2);
	__VERIFIER_assert(res1 == res2); 

	return 0;
}

