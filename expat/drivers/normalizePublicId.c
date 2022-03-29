#include <stdlib.h>
#include "expat.h"

void normalizePublicId(XML_Char *publicId);

int euf_main(){
	#ifdef CBMC
	XML_Char* publicId1;
	XML_Char* publicId2;

	//__CPROVER_assume(publicId1 == publicId2);

	normalizePublicId(publicId1);
	normalizePublicId(publicId2);
	
	__CPROVER_assert(publicId1 == publicId2, "Equivalent output");
	#endif

	return 0;
}

#if 0
static void FASTCALL
normalizePublicId(XML_Char *publicId) {
  XML_Char *p = publicId;
  XML_Char *s;
  for (s = publicId; *s; s++) {
    switch (*s) {
    case 0x20:
    case 0xD:
    case 0xA:
      if (p != publicId && p[-1] != 0x20)
        *p++ = 0x20;
      break;
    default:
      *p++ = *s;
    }
  }
  if (p != publicId && p[-1] == 0x20)
    --p;
  *p = XML_T('\0');
}
#endif
