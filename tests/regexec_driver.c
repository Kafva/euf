#include "cprover_builtin_headers.h"
#include <oniguruma.h>
#include <string.h>
#include <stdlib.h>

extern int nondet_int();
extern int* nondet_int_pointer();

// Example of a function to check
//	extern int onig_number_of_captures(regex_t* reg)
// This does not have any changes and should thus be a base case 
// that we detect as equivalent


int main(int argc, char* argv[]){
	regex_t* reg1;
	OnigErrorInfo einfo1;
	unsigned char* pattern1;

	onig_new(&reg1, pattern1, pattern1 + strlen((char* )pattern1),
        ONIG_OPTION_DEFAULT, ONIG_ENCODING_ASCII, ONIG_SYNTAX_DEFAULT, &einfo1);
	
	regex_t* reg2;
	OnigErrorInfo einfo;
	unsigned char* pattern2;

	onig_new(&reg2, pattern2, pattern2 + strlen((char* )pattern2),
        ONIG_OPTION_DEFAULT, ONIG_ENCODING_ASCII, ONIG_SYNTAX_DEFAULT, &einfo1);

	__CPROVER_assume( reg1 == reg2 );

	int res1 = onig_number_of_captures(reg1);
	int res2 = onig_number_of_captures(reg2);
	
	__CPROVER_assert(res1 == res2, "Equivalent behaviour");
	return 0;
}


