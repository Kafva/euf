#include <stdio.h>
// Introduced in b1d039607 and no changes has occured since
//	static unsigned long
//	getDebugLevel(const char *variableName, unsigned long defaultDebugLevel);
//	
//	static unsigned long
//	getDebugLevel_old_b026324c6904b2a(const char *variableName, unsigned long defaultDebugLevel);


int main(){
	unsigned long res 	  = getDebugLevel("test", 0);
	unsigned long res_old = getDebugLevel_old_b026324c6904b2a("test", 0);

	printf("%lu | %lu\n", res, res_old);

	return 0;
}
