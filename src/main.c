#include "strcpy.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int main(int argc, char* argv[]){
	//char* a = argv[0];
	char a[] = "ABCDEFGHIJ";


	/// To verify the equivalance of get_strsize with cbmc we need to
	/// have an assertion that verifies that the output for the same input does not differ 
	/// This can get extremely complex and is inherently limited: e.g. 
	///	We need to perform deep-copies of pointer arguments
	///	We can only use a limited --unwind depth
	unsigned size1 = get_strsize_1(a);
	unsigned size2 = get_strsize_2(a);

	assert( size1 == size2 );





	char b[40];
	dep_strcpy(b,a, get_strsize_1(a) );

	printf("a: %s\nb: %s\n", a, b);

	return 0;
}
