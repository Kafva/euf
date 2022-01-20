#include "strcpy.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int main(int argc, char* argv[]){
	char a[] = "ABCDEFGH";
	char b[40];

	dep_strcpy(b,a, sizeof(a)/sizeof(char) );

	printf("a: %s\nb: %s\n", a, b);


	// cbmc does not handle this without a --unwind > 10
	for (int i = 0; i < atoi(argv[1]); i++){
		assert(i < 10);
	}
	return 0;
}
