#include <stdlib.h>
#include "expat.h"

// Equiv change: 8650b04b2465f09a28199fcbd45747d49b6db3d8

XML_Bool keyeq(XML_Char* s1, XML_Char* s2);
// XML_Bool keyeq(XML_Char* s1, XML_Char* s2){
// 	return XML_FALSE;
// } 
XML_Bool keyeq_old_b026324c6904b2a(XML_Char* s1, XML_Char* s2); 


int euf_main(){
	#ifdef CBMC
	XML_Char* key1;
	XML_Char*	key2;

	XML_Bool res1 = keyeq(key1, key2);
	XML_Bool res2 = keyeq_old_b026324c6904b2a(key1, key2);
	
	__CPROVER_assert(res1 == res2, "Equivalent output");
	#endif
	return 0;
}

#if 0
static XML_Bool FASTCALL
keyeq_old_b026324c6904b2a(KEY s1, KEY s2) {
  for (; *s1 == *s2; s1++, s2++)
    if (*s1 == 0)
      return XML_TRUE;
  return XML_FALSE;
}
#endif

