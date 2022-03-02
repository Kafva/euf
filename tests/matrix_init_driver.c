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

//int* matrix_init_old(int rows, int columns, int limit)
////__CPROVER_requires(rows == DIM && columns == DIM) 
//{
//	int* matrix = malloc(rows*columns * sizeof(int));
//
//	for (int i = 0; i < rows; i++){
//		for (int j = 0; j < columns; j++){
//			printf("[%i*%i + %i =  %i]\n", i, columns, j, i*columns + j);
//			matrix[i*columns + j] = (i+j) % limit;
//		}
//	}
//	
//	return matrix;
//}
//
//int* matrix_init(int rows, int columns, int limit)
////__CPROVER_requires(rows == DIM && columns == DIM) 
//{
//	int* matrix = malloc(rows*columns * sizeof(int));
//
//	for (int i = 0; i < rows; i++){
//		for (int j = 0; j < columns; j++){
//			printf("[%i*%i + %i =  %i]\n", i, columns, j, i*columns + j);
//                        int val = 0;
//                        for (int x = 0; x < i+j; x++){
//                                val += 1;
//                        }
//                        matrix[i*columns + j] = val % limit;
//		}
//	}
//	
//	return matrix;
//}

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



