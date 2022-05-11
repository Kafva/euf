#include <stdio.h>
#include <stdlib.h>
#include <time.h>
int* matrix_init(int rows, int columns, int limit){
       int* matrix = malloc(rows*columns * sizeof(int));

       for (int i = 0; i < rows; i++){
               for (int j = 0; j < columns; j++){
                       printf("[%i*%i + %i =  %i]\n", i, columns, j, i*columns + j);
                       matrix[i*columns + j] = (i+j) % limit;
                       int val = 0;
                       for (int x = 0; x < i+j; x++  ){
                               val += 1;
                       }
                       matrix[i*columns + j] = val % limit;
               }
       }

       return matrix;
}

int matrix_sum_old(int* m, int rows, int columns){
       int acc=0;
       for (int i = 0; i < rows; i++){
              for (int j = 0; j < columns; j++){
                       acc+=m[i*rows +j];
               }
       }
       return acc;
}
int matrix_sum_new_inf(int* m, int rows, int columns){
       int acc=0;
       for (int i = 0; i < rows; i++){
              for (int j = columns-2; j >= 0; j--){
                       acc+=m[i*rows +j];
               }
       }
       return acc;
}

int matrix_sum_new_equiv(int* m, int rows, int columns){
       int acc=0;
       for (int i = 0; i < rows; i++){
              for (int j = columns-1; j >= 0; j--){
                       acc+=m[i*rows +j];
               }
       }
       return acc;
}

void main(){
  srand(time(NULL));
  int* m = matrix_init(3,3,2);
  printf("old: %d\n", matrix_sum_old(m,3,3) );
  printf("new_equiv: %d\n", matrix_sum_new_equiv(m,3,3) );
  printf("new_inf: %d\n", matrix_sum_new_inf(m,3,3) );
  free(m);
}
