#include <stdlib.h>
#include <limits.h>
#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include "smack.h"

int PERSON_GLOB = 31;

enum Gender  {
	Male,Female,Other
};

typedef struct Person  {
	// char* name;
	char name[50];
	unsigned age;
	enum Gender gender;
} Person;
	
bool eq(struct Person* self, struct Person* other) {
	return self->age == other->age && self->gender == other->gender &&
		strcmp(self->name, other->name) == 0;
}

void smack_assert(Person* p) {
  __SMACK_code("assert @ != 0;", p);
}
void smack_assume(Person* p) {
  __SMACK_code("assume @ != 0;", p);
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
	// - - - Struct* - - -
	// To verify manipulated pointers we need to manually define equality operators
	//
	// We need a way of telling the verifier that p1 and p2 cannot be NULL (if that is the case in reality?)
	// This should be possible by using inline Boogie code

	//Person p1 = { .name = __VERIFIER_nondet_pointer(), .age = 12, .gender = Other };
	//Person p2 = { .name = __VERIFIER_nondet_pointer(), .age = 12, .gender = Other };

	
	//Person* p1 = __VERIFIER_nondet_pointer();  
	//Person* p2 = __VERIFIER_nondet_pointer(); 


	//assume( p1 != NULL && p2 != NULL );
	//assume( strlen(p1->name) > 4 && strlen(p2->name)  > 4 );
	//assume( p1->name == p2->name );
	
	//smack_assume(p1);
	//smack_assume(p2);

	//set_age_1(p1);
	//set_age_2(p2);
	//assert( eq(p1, p2) );

	// - - - Struct* - - -
	// Person p = { .name = "Max", .age = 12, .gender = Other };
	void* p = __VERIFIER_nondet_pointer();  // { .name = "Max", .age = 12, .gender = Other };
	unsigned age1 = get_age_1(p);
	unsigned age2 = get_age_2(p);
	assert( age1 == age2 );



	// - - - Char* - - -
	//char* a = __VERIFIER_nondet_pointer();
	//unsigned size1 = get_strsize_1(a);
	//unsigned size2 = get_strsize_2(a);
	//assert( size1 == size2 );
	
	// - - - Scalar type - - -
	//unsigned int a = __VERIFIER_nondet_uint();
	//unsigned mod1 = get_mod_1(a);
	//unsigned mod2 = get_mod_2(a);
	//assert( mod1 == mod2 );

	return 0;
}



//---------------------------------------------//
//void set_age_1(Person* p){
//	p->age = 12;
//}
//
//void set_age_2(Person* p){
//	p->age = 12;
//}
//unsigned get_strsize_1(char* str){
//	unsigned size = 0;
//
//	while (1) {
//		if (*(str+size) == '\0') break;
//		size++;
//	}
//	
//	return size + 1; 
//}
//
//unsigned get_strsize_2(char* str){
//	unsigned size = 0;
//
//	while (1) {
//		if (*(str+size) == '\0') break;
//		size++;
//		if (size%2 == 0) size++;
//	}
//	
//	return size + 1; 
//}


//unsigned get_mod_1(unsigned int k){
//	return k % 5; 
//}
//
//unsigned get_mod_2(unsigned int k){
//	return k % 5; 
//}

