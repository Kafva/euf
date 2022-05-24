int nondet_int();
int main(){
  int a = nondet_int();
  int b = nondet_int();
  a = a + b;

  if (a < 9)
    a = 10;
  else
    b = 5;

  __CPROVER_assert(a+b<=15, 
      "main always returns a value below or equal to 15"
  );
  return a+b;
}
