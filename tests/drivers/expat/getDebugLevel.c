// Introduced in b1d039607 and no changes has occured since
#include <stdlib.h>
#include "expat.h"

unsigned long // We need this decleration since the original is only defined
							// inside lib/xmlparse.c
getDebugLevel(const char *variableName, unsigned long defaultDebugLevel);

unsigned long 
getDebugLevel_old_b026324c6904b2a(const char *variableName, unsigned long defaultDebugLevel);

int euf_main(){
	#ifdef CBMC
	char* varname1;
	char* varname2;
	unsigned long defaultLevel1, defaultLevel2;

	__CPROVER_assume(defaultLevel1 == defaultLevel2 && varname1 == varname2);

	unsigned long res 				= getDebugLevel(varname1, defaultLevel1);
	unsigned long res_old 		= getDebugLevel_old_b026324c6904b2a(varname2, defaultLevel2);

	__CPROVER_assert(res == res_old, "Equivalent output");
	#endif

	return 0;
}


#if 0
unsigned long
getDebugLevel(const char *variableName, unsigned long defaultDebugLevel) {
  const char *const valueOrNull = getenv(variableName);
  if (valueOrNull == NULL) {
    return defaultDebugLevel;
  }
  const char *const value = valueOrNull;

  errno = 0;
  char *afterValue = (char *)value;
  unsigned long debugLevel = strtoul(value, &afterValue, 10);
  if ((errno != 0) || (afterValue[0] != '\0')) {
    errno = 0;
    return defaultDebugLevel;
  }

  return debugLevel;
}
#endif
