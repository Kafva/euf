#include "strcpy.h"
#include <stdio.h>

int main(){
	char a[] = "ABCDEFGH";
	char b[40];

	dep_strcpy(b,a, sizeof(a)/sizeof(char) );

	printf("a: %s\nb: %s\n", a, b);

	return 0;
}
