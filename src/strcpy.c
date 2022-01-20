#include "strcpy.h"

void dep_strcpy(char* dst, char* src, size_t size) {
	for (unsigned i = 0; i < size; i++) {
		dst[i]=src[i];	
		if(src[i]=='\0')break; // Stop on NULL
	}
}

/// To verify the equivalance of get_strsize with cbmc we need to
/// have an assertion that verifies that the output for the same input does not differ 
/// This can get extremely complex and is inherently limited: e.g. 
///	We need to perform deep-copies of pointer arguments
///	We can only use a limited --unwind depth
unsigned get_strsize_1(char* str){
	unsigned length = 0;
	while (1) {
		if (*(str+length) == '\0') break;
		length++;
	}
	
	length++;
	__CPROVER_assert(length == get_strsize_2(str), "get_strsize() output differs");
	return length; 
}

unsigned get_strsize_2(char* str){
	unsigned length = 0;
	while (1) {
		if (*(str+length) == '\0') break;
		if (*(str+length) == 'F' ) length++; 
		length++;
	}
	
	return length; 
}

