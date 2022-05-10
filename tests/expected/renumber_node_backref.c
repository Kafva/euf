// direct change: a/src/regcomp.c:1824:1:renumber_node_backref() -> b/src/regcomp.c:2026:1:renumber_node_backref()
#ifdef CBMC
#include <stdlib.h>
#include <features.h>
#include <features-time64.h>
#include <stdc-predef.h>
#include <sys/cdefs.h>
#include <gnu/stubs.h>
#include <gnu/stubs-64.h>
#include <sys/types.h>
#include <endian.h>
#include <sys/select.h>
#include <alloca.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <limits.h>
#include <linux/limits.h>


#include "regcomp.h"


#include "src/regparse.h"
#include "src/regint.h"
#include "src/config.h"
#include "src/regenc.h"
#include "src/oniguruma.h"

struct _Node* nondet_Node();
GroupNumRemap* nondet_GroupNumRemap();

int renumber_node_backref_old_b026324c6904b2a(struct _Node* node, GroupNumRemap* map);
int renumber_node_backref(struct _Node* node, GroupNumRemap* map);

void euf_main() {
  struct _Node* node = nondet_Node();
  GroupNumRemap* map = nondet_GroupNumRemap();


  int ret_old = renumber_node_backref_old_b026324c6904b2a(node, map);
  int ret = renumber_node_backref(node, map);

  __CPROVER_assert(ret_old == ret, "Equivalent output");
}
#endif
