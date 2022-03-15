#include <stdio.h>
int main(){
	char* multi = " \
	multiline string \
	over \
	\"here\" \
	"; 

	char* myself = "myself"; printf("How does onemyself \"%s\" explain myself?\n", myself);
	char* self = """a""";
	printf("%s\n", self);

	char n = '\n'; 
	
	char* n2 = "'\n'"; 

	return 0;
}

