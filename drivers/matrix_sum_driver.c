#include "cprover_builtin_headers.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define DIM 3

int matrix_sum(int* m, int rows, int columns);
int matrix_sum_old_b026324c6904b2a(int* m, int rows, int columns);

// extern int* nondet_int_pointer();
extern int  nondet_int();


int* m_init(int rows, int columns){
	int* matrix = malloc(sizeof(int)*rows*columns);
	for (int i = 0; i < rows; i++){
		for (int j = 0; j < columns; j++){
			matrix[i*columns + j] = nondet_int();
		}
	}
	return matrix;
}


int main(int argc, char* argv[]){
	//int* m1 = nondet_int_pointer();
	//int* m2 = nondet_int_pointer();
	
	int* m1 = m_init(DIM,DIM);
	int* m2 = m_init(DIM,DIM);

	for (int i = 0; i < DIM; i++){
		for (int j = 0; j < DIM; j++){
			__CPROVER_assume(m1[i*DIM + j] == m2[i*DIM + j]);
		}
	}

	int res1 = matrix_sum_old_b026324c6904b2a(m1,DIM,DIM);
	int res2 = matrix_sum(m2,DIM,DIM);
	__CPROVER_assert(res1 == res2, "Equivalent behaviour"); 

	free(m1);
	free(m2);

	return 0;
}


