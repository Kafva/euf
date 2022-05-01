// direct change: a/expat/lib/xmlparse.c:801:1:ENTROPY_DEBUG() -> b/expat/lib/xmlparse.c:891:1:ENTROPY_DEBUG()
#ifdef CBMC
#include <string.h>
#include <features.h>
#include <features-time64.h>
#include <stdc-predef.h>
#include <sys/cdefs.h>
#include <gnu/stubs.h>
#include <gnu/stubs-64.h>
#include <strings.h>
#include <assert.h>
#include <limits.h>
#include <linux/limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <endian.h>
#include <sys/select.h>
#include <alloca.h>
#include <stdint.h>
#include <sys/time.h>
#include <unistd.h>
#include <linux/close_range.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <errno.h>
#include <linux/errno.h>
#include <asm/errno.h>
#include <asm-generic/errno.h>
#include <asm-generic/errno-base.h>
#include <sys/random.h>


#include "xmlparse.h"


#include "expat_config.h"
#include "lib/ascii.h"
#include "lib/expat.h"
#include "lib/expat_external.h"
#include "lib/siphash.h"
#include "lib/internal.h"
#include "lib/xmltok.h"
#include "lib/xmlrole.h"

unsigned long ENTROPY_DEBUG_old_b026324c6904b2a(const char* label, unsigned long entropy);
unsigned long ENTROPY_DEBUG(const char* label, unsigned long entropy);

void euf_main() {
  const char* label;
  unsigned long entropy;

  __CPROVER_assume(
    label == "/dev/urandom" ||
    label == "fallback(4)" ||
    label == "fallback(8)" ||
    label == "getrandom"
  );

  unsigned long ret_old = ENTROPY_DEBUG_old_b026324c6904b2a(label, entropy);
  unsigned long ret = ENTROPY_DEBUG(label, entropy);

  __CPROVER_assert(ret_old == ret, "Equivalent output");
}
#endif
