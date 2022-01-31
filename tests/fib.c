#include <stdio.h>
const int n = 9;

int fib(int k) {
	if ( k<=1 ) return 1;
	else return fib(k-1) + k;
}

int main(){
	printf("%d\n", fib(n) );
	return 0;
}
