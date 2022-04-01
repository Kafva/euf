//int new_size(int);
//int new_size_old_b026324c6904b2a(int);
//#include "oniguruma_new.h"
//#include "oniguruma_old.h"


// We test a simple function that has not changed as a basecase
// 	st.c: int new_size(int)
int main(int argc, char* argv[]){
#ifdef CBMC
	// - - - Init - - -
	int size1 = nondet_int();
	int size2 = nondet_int();
	__CPROVER_assume( 0 < size1 && size1 < 10 );
	__CPROVER_assume( 0 < size2 && size2 < 10 );
	__CPROVER_assume( size1 == size1 );
	

	int ret_old = new_size_old_b026324c6904b2a(size1);
	int ret_new = new_size(size2);

	// - - - Assert - - -
	__CPROVER_assert(ret_old == ret_new, "Equivalent behaviour");
#endif
	return 0;
}
