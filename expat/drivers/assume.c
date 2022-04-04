int euf_main(){
	#ifdef CBMC

  // An assumption does not infer that the given
  // condition will be auto-resolved for the rest of
  // the verification process
  int x = 5;

  int y;
  __CPROVER_assume(x==y);
  //y=6;
  __CPROVER_assert(x==y, "Same");

	#endif
	return 0;
}


