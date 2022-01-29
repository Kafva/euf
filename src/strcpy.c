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

char* get_heap_str(char* str){
	unsigned size = get_strsize_1(str);
	char* heap_str = (char*)malloc( sizeof(char)*size );	
	dep_strcpy(heap_str, str, size);
	return heap_str;
}


void free_heap_str(char* str){
	free(str);
}
