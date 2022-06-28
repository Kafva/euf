int nondet_int();
int sum_old(int a, int b){ return a+b; }
int sum(int a, int b){ return a-b; /*???*/ }

void euf_main(){
  int x = nondet_int();
  int y = nondet_int();
  int ret_old = sum_old(x,y);
  int ret = sum(x,y);
  __CPROVER_assert(ret_old == ret, "Equivalent output");
}

