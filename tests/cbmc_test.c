#include "cprover_builtin_headers.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

extern int nondet_int();

enum Gender  {
	Male,Female,Other
};

typedef struct Person  {
	char* name;
	unsigned age;
	enum Gender gender;
} Person;
	
int eq(struct Person* self, struct Person* other) {
	return self->age == other->age && self->gender == other->gender;
}

unsigned get_strsize_1(char* str){
	unsigned size = 0;

	while (1) {
		if (*(str+size) == '\0') break;
		size++;
	}
	
	return size + 1; 
}

unsigned get_strsize_2(char* str){
	unsigned size = 0;

	while (1) {
		if (*(str+size) == '\0') break;
		size++;
		if (size%2 == 0) size++;
	}
	
	return size + 1; 
}

unsigned get_age_1(Person* p){
	return p->age; 
}

unsigned get_age_2(Person* p){
	unsigned x = p->age;
	x += 0;
	return x;
}


int main(int argc, char* argv[]){
	//__CPROVER_precondition(argv[0] != NULL, "Assume non-null input");
	//__CPROVER_assume(argv[0] != NULL); 

	unsigned age1 = nondet_int();
	unsigned age2 = nondet_int();
	__CPROVER_assume(age1 == age2);

	Person p1 = { .name = "Max", .age = age1, .gender = Other };
	Person p2 = { .name = "Max", .age = age2, .gender = Other };

	
	unsigned res1 = get_age_1(&p1);
	unsigned res2 = get_age_2(&p2);
	__CPROVER_assert(res1 == res2, "Equivalent behaviour"); 

	return 0;
}

