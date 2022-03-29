#include <stdlib.h>
//#include "expat_old.h"

// Required!
#include "expat.h" // Has the decleration for types 
									 // and the new version of XML_ErrorString
const XML_LChar *XMLCALL
XML_ErrorString_old_b026324c6904b2a(enum XML_Error code);

int euf_main(){
	#ifdef CBMC
	enum XML_Error code = nondet_int();
	XML_LChar out1 = XML_ErrorString(code);
	XML_LChar out2 = XML_ErrorString_old_b026324c6904b2a(code);

	__CPROVER_assert(out1 == out2, "Same");
	#endif

	return 0;
}


