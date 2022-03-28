#include <stdlib.h>
#define DIM 3

int* matrix_init_old_b026324c6904b2a(int rows, int columns, int limit);
int* matrix_init(int rows, int columns, int limit);

int euf_main(int argc, char* argv[]){
	#ifdef CBMC
	int limit = nondet_int();
	__CPROVER_assume( limit > 0 );

	int* m1 = matrix_init_old_b026324c6904b2a(DIM,DIM,limit);
	int* m2 = matrix_init(DIM,DIM,limit);

	for (int i = 0; i < DIM; i++){
		for (int j = 0; j < DIM; j++){
			__CPROVER_assert(
				m1[i*DIM + j] == m2[i*DIM + j], 
				"Equivalent behaviour"
			);
		}
	}

	free(m1);
	free(m2);
	#endif

	return 0;
}



