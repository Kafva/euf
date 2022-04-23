#include <stdlib.h>
#include "expat.h"


XML_Bool keyeq_old_b026324c6904b2a(XML_Char* s1, XML_Char* s2){
  s1=s1+1;
	return XML_FALSE;
} 

XML_Bool keyeq(XML_Char* s1, XML_Char* s2){
  s1=s1+1;
	return XML_FALSE;
} 


int euf_main(){
	#ifdef CBMC
	XML_Char* key1_old;
	XML_Char*	key2_old;
	
  XML_Char* key1;
	XML_Char*	key2;


  //__CPROVER_assume(key1_old == key1 && key2_old == key2);
  __CPROVER_assume(*key1_old == *key1 && *key2_old == *key2);
  __CPROVER_assume(*(key1_old+1) == *(key1+1));

	XML_Bool res_old  = keyeq_old_b026324c6904b2a(key1_old, key2_old);
	XML_Bool res      = keyeq(key1, key2);

  __CPROVER_assert(
       //__CPROVER_POINTER_OBJECT(key1_old) == 
       //__CPROVER_POINTER_OBJECT(key1), 
       __CPROVER_POINTER_OFFSET(key1_old) == 
       __CPROVER_POINTER_OFFSET(key1), 
       //*key1_old == *key1,

       "Equivalent output"
  );

	//__CPROVER_assert(res_old == res, "Equivalent output");
	#endif
	return 0;
}

