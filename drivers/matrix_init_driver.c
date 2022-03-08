#include "cprover_builtin_headers.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// Explicit forward declerations are usually neccessary
int* matrix_init(int rows, int columns, int limit);
int* matrix_init_old(int rows, int columns, int limit);

#define DIM 3

// extern int* nondet_int_pointer();
extern int nondet_int();

int main(int argc, char* argv[]){
	//int* m1 = nondet_int_pointer();
	//int* m2 = nondet_int_pointer();
	
	int limit = nondet_int();
	__CPROVER_assume( limit > 0 );

	int* m1 = matrix_init_old(DIM,DIM,limit);
	int* m2 = matrix_init(DIM,DIM,limit);

	for (int i = 0; i < DIM; i++){
		for (int j = 0; j < DIM; j++){
			__CPROVER_assert(m1[i*DIM + j] == m2[i*DIM + j], "Same result");
			//printf("%d:%d %d:%d\n",i*DIM + j,  m1[i*DIM + j] ,i*DIM + j, m2[i*DIM + j]);
			//assert(m1[i*DIM + j] == m2[i*DIM + j]);
		}
	}

	free(m1);
	free(m2);

	return 0;
}



