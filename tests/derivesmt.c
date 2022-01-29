#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>

void dep_strcpy(char* dst, char* src, size_t size) {
	for (unsigned i = 0; i < size; i++) {
		dst[i]=src[i];	
		if(src[i]=='\0')break; // Stop on NULL
	}
}

unsigned get_strsize(char* str){
	unsigned size = 0;

	while (1) {
		if (*(str+size) == '\0') break;
		size++;
	}
	
	return size + 1; 
}

int main(int argc, char* argv[], char* envp[]) {

	char a[60];

	if (argc > 1){
		unsigned size = get_strsize(argv[1]);
		dep_strcpy(a, argv[1], size);
	} else {
		const char default_str[] = "ABCDEFGHI"; 
		dep_strcpy(a, (char*)default_str, sizeof(default_str));
	}

	printf("a = %s\n", a);

	return 0;
}
