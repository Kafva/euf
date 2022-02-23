#include <stdlib.h>
#include <limits.h>
#include <assert.h>
#include <stdio.h>
#include "smack.h"

unsigned get_strsize_1(char* str){
	unsigned size = 0;

	while (1) {
		if (*(str+size) == '\0') break;
		size++;
	}
	
	return size + 1; 
}

unsigned get_strsize_2(char* str){
	unsigned size = 0;

	while (1) {
		if (*(str+size) == '\0') break;
		size++;
		if (size%2 == 0) size++;
	}
	
	return size + 1; 
}

//unsigned get_mod_1(unsigned int k){
//	return k % 5; 
//}
//
//unsigned get_mod_2(unsigned int k){
//	return k % 5; 
//}


int main(int argc, char* argv[]){
	char* a = __VERIFIER_nondet_pointer();
	unsigned size1 = get_strsize_1(a);
	unsigned size2 = get_strsize_2(a);
	assert( size1 == size2 );
	
	//unsigned int a = __VERIFIER_nondet_uint();
	//unsigned mod1 = get_mod_1(a);
	//unsigned mod2 = get_mod_2(a);
	//assert( mod1 == mod2 );

	return 0;
}

