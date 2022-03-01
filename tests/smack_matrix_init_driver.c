#include "smack.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// Explicit forward declerations are usually neccessary
int* matrix_init(int rows, int columns, int limit);
int* matrix_init_old(int rows, int columns, int limit);

#define DIM 3

int main(int argc, char* argv[]){
	int seed = __VERIFIER_nondet_int();
	int* m1 = matrix_init_old(DIM,DIM,seed);
	int* m2 = matrix_init(DIM,DIM,seed);

	for (int i = 0; i < DIM; i++){
		for (int j = 0; j < DIM; j++){
			__VERIFIER_assert(m1[i*DIM + j] == m2[i*DIM + j]);
		}
	}

	free(m1);
	free(m2);

	return 0;
}




