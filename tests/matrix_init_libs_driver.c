#ifdef CBMC
	#include "cprover_builtin_headers.h"
	extern int nondet_int();
	extern int* nondet_int_pointer();
#endif

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// Explicit forward declerations are usually neccessary
int* matrix_init(int rows, int columns, int limit);
int* matrix_init_old(int rows, int columns, int limit);

#define DIM 3

int main(int argc, char* argv[]){

	#ifdef CBMC
	int limit = nondet_int();
	__CPROVER_assume( limit > 0 );
	#else
	int limit = 10;
	#endif


	int* m1 = matrix_init_old(DIM,DIM,limit);
	int* m2 = matrix_init(DIM,DIM,limit);

	for (int i = 0; i < DIM; i++){
		for (int j = 0; j < DIM; j++){
			#ifdef CBMC
			__CPROVER_assert(m1[i*DIM + j] == m2[i*DIM + j], "Same result");
			#else
			printf("%d:%d %d:%d\n",i*DIM + j,  m1[i*DIM + j] ,i*DIM + j, m2[i*DIM + j]);
			assert(m1[i*DIM + j] == m2[i*DIM + j]);
			#endif
		}
	}

	free(m1);
	free(m2);

	return 0;
}





