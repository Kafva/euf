// Introduced in b1d039607 and no changes has occured since
//extern unsigned long
//getDebugLevel(const char *variableName, unsigned long defaultDebugLevel);
// extern unsigned long
// getDebugLevel_old_b026324c6904b2a(const char *variableName, unsigned long defaultDebugLevel);

#include <stdlib.h>

int errno;

static unsigned long
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

int main(){
	#ifdef CBMC

	//unsigned long res 	  	= getDebugLevel("test", 0);
	//unsigned long res1 			= getDebugLevel$link1("test", 0);
	//unsigned long res2 			= getDebugLevel$link2("test", 0);
	//unsigned long res_old 	= getDebugLevel_old_b026324c6904b2a("test", 0);
	//unsigned long res_old1 	= getDebugLevel_old_b026324c6904b2a$link1("test", 0);
	//unsigned long res_old2 	= getDebugLevel_old_b026324c6904b2a$link2("test", 0);
	
	//char* varname1;
	//char* varname2;
	unsigned long defaultLevel1, defaultLevel2;
	//__CPROVER_assume( defaultLevel1 == defaultLevel2 && varname1 == varname2 );

	unsigned long res 				= getDebugLevel("aaaa", 0);
	unsigned long res_old 		= getDebugLevel("aaaa", 0);
	//unsigned long res_old = getDebugLevel_old_b026324c6904b2a("test", 0);

	__CPROVER_assert(res == res_old, "Same");
	#endif

	return 0;
}
