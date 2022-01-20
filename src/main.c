#include "strcpy.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int main(int argc, char* argv[]){
	char a[] = "ABCDEFGH";
	char b[40];



	unsigned size1 = get_strsize_1(a);
	unsigned size2 = get_strsize_2(a);

	assert( size1 == size2 );




	dep_strcpy(b,a, get_strsize_1(a) );

	printf("a: %s\nb: %s\n", a, b);

	return 0;
}
