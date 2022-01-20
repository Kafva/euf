#include "strcpy.h"

void dep_strcpy(char* dst, char* src, size_t size) {
	for (unsigned i = 0; i < size; i++) {
		dst[i]=src[i];	
		if(src[i]=='\0')break; // Stop on NULL
	}
}

unsigned get_strsize_1(char* str){
	unsigned size = 0;
	while (1) {
		if (*(str+size) == '\0') break;
		size++;
	}
	
	size++;

	return size; 
}

unsigned get_strsize_2(char* str){
	unsigned size = 0;
	unsigned debug = 0;
	while (1) {
		if (*(str+size) == '\0') break;
		if (*(str+size) == 'F' ) debug++; 
		
		size++;
		if (size%4 == 0) size++;
	}
	
	size++;

	return size; 
}

