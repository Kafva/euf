#include "cprover_builtin_headers.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

extern int nondet_int();
int main(int argc, char* argv[]){

	unsigned sum1 = nondet_int();
	unsigned sum2 = nondet_int();
	__CPROVER_assume(age1 == age2);

	Person p1 = { .name = "Max", .age = age1, .gender = Other };
	Person p2 = { .name = "Max", .age = age2, .gender = Other };

	
	unsigned res1 = get_age_1(&p1);
	unsigned res2 = get_age_2(&p2);
	__CPROVER_assert(res1 == res2, "Equivalent behaviour"); 

	return 0;
}

