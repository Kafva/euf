#include <stdlib.h>
//#include "expat_new.h"

//static size_t
//poolBytesToAllocateFor(int blockSize);
//
//static size_t
//poolBytesToAllocateFor_old_b026324c6904b2a(int blockSize);

int euf_main(){
	#ifdef CBMC
	
	int blockSize = nondet_int();
	__CPROVER_assume(blockSize > 0);

	size_t res 				= poolBytesToAllocateFor(blockSize);
	size_t res_old 		= poolBytesToAllocateFor_old_b026324c6904b2a(blockSize);
	

	//res 				= poolBytesToAllocateFor$link1(blockSize);
	//res_old 		= poolBytesToAllocateFor_old_b026324c6904b2a$link1(blockSize);
	//
	//res 				= poolBytesToAllocateFor$link2(blockSize);
	//res_old 		= poolBytesToAllocateFor_old_b026324c6904b2a$link2(blockSize);
	//
	//res 				= poolBytesToAllocateFor$link3(blockSize);
	//res_old 		= poolBytesToAllocateFor_old_b026324c6904b2a$link3(blockSize);

	__CPROVER_assert(res == res_old, "Same");
	#endif

	return 0;
}

