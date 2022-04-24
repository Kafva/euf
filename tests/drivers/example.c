int sum(int a, int b){ return a+b; }

void euf_main(){
  #ifdef CBMC
  int x = nondet_int();
  int y = nondet_int();
  __CPROVER_assert(sum(x,y)==x+y, "Expected behaviour");
  #endif
}

