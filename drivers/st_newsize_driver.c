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
	

	int ret_old = new_size_old(size1);
	int ret_new = new_size(size2);

	// - - - Assert - - -
	__CPROVER_assert(ret_old == ret_new, "Equivalent behaviour");
#endif
	return 0;
}
