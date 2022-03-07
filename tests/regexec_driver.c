#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#ifdef CBMC
	#include "cprover_builtin_headers.h"
	extern int nondet_int();
	extern int* nondet_int_pointer();
#endif

// - - - Initialisation code based on test/testc.c - - -
// The definitions for onig_new(), onig_end() etc. are found in 
// 	src/regcomp.c
//
// The easiest way of accessing all of the initalisation functions
// is to link agianst the finished library 
// 		/usr/lib/libonig.so
// 		./src/.libs/libonig.a
// 		./.libs/libonig.a
//
// This will however give us multiple definitions for the functions we
// want to test... 
// If we used a _new and _old suffix on the functions in the change set...
//
// We could use a _new renaming scheme as well to avoid this...
// to some extent...
#include <oniguruma.h>
static OnigRegion* region;

regex_t* regex_init(char* pattern, char* str, int from, int to) {
	int r;
	regex_t* reg;
	OnigErrorInfo einfo;

	r = onig_new(&reg, (UChar* )pattern, (UChar* )(pattern + strlen(pattern)),
		ONIG_OPTION_DEFAULT, ONIG_ENCODING_EUC_JP, ONIG_SYNTAX_DEFAULT, &einfo
	);
	if (r) {
		char s[ONIG_MAX_ERROR_MESSAGE_LEN];
		onig_error_code_to_str((UChar* )s, r, &einfo);
		fprintf(stderr, "ERROR: %s\n", s);
		return NULL;
	}
	return reg;
}

int main(int argc, char* argv[]){
	// - - - Init - - -
	#ifdef CBMC
	// Uninitialised variables are automatically treated as 'nondet' by CBMC
	char* pattern;
	char* str;
	int from, to;
	__CPROVER_assume( 0 < from && from < to );
	__CPROVER_assume( strlen(pattern) > 0 && strlen(str) > 0 && strlen(pattern) < 100 && strlen(str) < 100 );
	#else
	char* pattern = "haystack and needle";
	char* str = "needle";
	int from = 0, to = 5;
	#endif

	OnigEncoding use_encs[1];

	use_encs[0] = ONIG_ENCODING_EUC_JP;
	onig_initialize(use_encs, sizeof(use_encs)/sizeof(use_encs[0]));

	region = onig_region_new();

	regex_t* reg1 = regex_init(pattern, str, from, to);
	regex_t* reg2 = regex_init(pattern, str, from, to);
	// - - - - - - - -
	
	#ifdef CBMC
	__CPROVER_assume( reg1 == reg2 );

	int res1 = onig_number_of_captures(reg1);
	int res2 = onig_number_of_captures(reg2);
	
	__CPROVER_assert(res1 == res2, "Equivalent behaviour");
	#endif
	
	onig_region_free(region, 1);
	onig_end();

	return 0;
}


