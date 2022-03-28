/*
                            __  __            _
                         ___\ \/ /_ __   __ _| |_
                        / _ \\  /| '_ \ / _` | __|
                       |  __//  \| |_) | (_| | |_
                        \___/_/\_\ .__/ \__,_|\__|
                                 |_| XML parser

   Copyright (c) 1997-2000 Thai Open Source Software Center Ltd
   Copyright (c) 2000      Clark Cooper <coopercc@users.sourceforge.net>
   Copyright (c) 2002      Greg Stein <gstein@users.sourceforge.net>
   Copyright (c) 2002-2006 Karl Waclawek <karl@waclawek.net>
   Copyright (c) 2002-2003 Fred L. Drake, Jr. <fdrake@users.sourceforge.net>
   Copyright (c) 2005-2009 Steven Solie <steven@solie.ca>
   Copyright (c) 2016-2021 Sebastian Pipping <sebastian@pipping.org>
   Copyright (c) 2017      Rhodri James <rhodri@wildebeest.org.uk>
   Copyright (c) 2019      David Loffredo <loffredo@steptools.com>
   Copyright (c) 2021      Dong-hee Na <donghee.na@python.org>
   Licensed under the MIT license:

   Permission is  hereby granted,  free of charge,  to any  person obtaining
   a  copy  of  this  software   and  associated  documentation  files  (the
   "Software"),  to  deal in  the  Software  without restriction,  including
   without  limitation the  rights  to use,  copy,  modify, merge,  publish,
   distribute, sublicense, and/or sell copies of the Software, and to permit
   persons  to whom  the Software  is  furnished to  do so,  subject to  the
   following conditions:

   The above copyright  notice and this permission notice  shall be included
   in all copies or substantial portions of the Software.

   THE  SOFTWARE  IS  PROVIDED  "AS  IS",  WITHOUT  WARRANTY  OF  ANY  KIND,
   EXPRESS  OR IMPLIED,  INCLUDING  BUT  NOT LIMITED  TO  THE WARRANTIES  OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
   NO EVENT SHALL THE AUTHORS OR  COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
   DAMAGES OR  OTHER LIABILITY, WHETHER  IN AN  ACTION OF CONTRACT,  TORT OR
   OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
   USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

#include <expat_config.h>

#include <stddef.h>

#ifdef _WIN32
#  include "winconfig.h"
#endif

#include "expat_external.h"
#include "internal.h"
#include "xmlrole.h"
#include "ascii.h"

/* Doesn't check:

 that ,| are not mixed in a model group
 content of literals

*/

static const char KW_ANY[] = {ASCII_A, ASCII_N, ASCII_Y, '\0'};
static const char KW_ATTLIST[]
    = {ASCII_A, ASCII_T, ASCII_T, ASCII_L, ASCII_I, ASCII_S, ASCII_T, '\0'};
static const char KW_CDATA[]
    = {ASCII_C, ASCII_D, ASCII_A, ASCII_T, ASCII_A, '\0'};
static const char KW_DOCTYPE[]
    = {ASCII_D, ASCII_O, ASCII_C, ASCII_T, ASCII_Y, ASCII_P, ASCII_E, '\0'};
static const char KW_ELEMENT[]
    = {ASCII_E, ASCII_L, ASCII_E, ASCII_M, ASCII_E, ASCII_N, ASCII_T, '\0'};
static const char KW_EMPTY[]
    = {ASCII_E, ASCII_M, ASCII_P, ASCII_T, ASCII_Y, '\0'};
static const char KW_ENTITIES[] = {ASCII_E, ASCII_N, ASCII_T, ASCII_I, ASCII_T,
                                   ASCII_I, ASCII_E, ASCII_S, '\0'};
static const char KW_ENTITY[]
    = {ASCII_E, ASCII_N, ASCII_T, ASCII_I, ASCII_T, ASCII_Y, '\0'};
static const char KW_FIXED[]
    = {ASCII_F, ASCII_I, ASCII_X, ASCII_E, ASCII_D, '\0'};
static const char KW_ID[] = {ASCII_I, ASCII_D, '\0'};
static const char KW_IDREF[]
    = {ASCII_I, ASCII_D, ASCII_R, ASCII_E, ASCII_F, '\0'};
static const char KW_IDREFS[]
    = {ASCII_I, ASCII_D, ASCII_R, ASCII_E, ASCII_F, ASCII_S, '\0'};
#ifdef XML_DTD
static const char KW_IGNORE[]
    = {ASCII_I, ASCII_G, ASCII_N, ASCII_O, ASCII_R, ASCII_E, '\0'};
#endif
static const char KW_IMPLIED[]
    = {ASCII_I, ASCII_M, ASCII_P, ASCII_L, ASCII_I, ASCII_E, ASCII_D, '\0'};
#ifdef XML_DTD
static const char KW_INCLUDE[]
    = {ASCII_I, ASCII_N, ASCII_C, ASCII_L, ASCII_U, ASCII_D, ASCII_E, '\0'};
#endif
static const char KW_NDATA[]
    = {ASCII_N, ASCII_D, ASCII_A, ASCII_T, ASCII_A, '\0'};
static const char KW_NMTOKEN[]
    = {ASCII_N, ASCII_M, ASCII_T, ASCII_O, ASCII_K, ASCII_E, ASCII_N, '\0'};
static const char KW_NMTOKENS[] = {ASCII_N, ASCII_M, ASCII_T, ASCII_O, ASCII_K,
                                   ASCII_E, ASCII_N, ASCII_S, '\0'};
static const char KW_NOTATION[] = {ASCII_N, ASCII_O, ASCII_T, ASCII_A, ASCII_T,
                                   ASCII_I, ASCII_O, ASCII_N, '\0'};
static const char KW_PCDATA[]
    = {ASCII_P, ASCII_C, ASCII_D, ASCII_A, ASCII_T, ASCII_A, '\0'};
static const char KW_PUBLIC[]
    = {ASCII_P, ASCII_U, ASCII_B, ASCII_L, ASCII_I, ASCII_C, '\0'};
static const char KW_REQUIRED[] = {ASCII_R, ASCII_E, ASCII_Q, ASCII_U, ASCII_I,
                                   ASCII_R, ASCII_E, ASCII_D, '\0'};
static const char KW_SYSTEM[]
    = {ASCII_S, ASCII_Y, ASCII_S, ASCII_T, ASCII_E, ASCII_M, '\0'};

#ifndef MIN_BYTES_PER_CHAR
#  define MIN_BYTES_PER_CHAR(enc) ((enc)->minBytesPerChar)
#endif

#ifdef XML_DTD
#  define setTopLevel(state)                                                   \
    ((state)->handler                                                          \
     = ((state)->documentEntity ? internalSubset_old_b026324c6904b2a : externalSubset1_old_b026324c6904b2a))
#else /* not XML_DTD */
#  define setTopLevel(state) ((state)->handler = internalSubset)
#endif /* not XML_DTD */

typedef int PTRCALL PROLOG_HANDLER(PROLOG_STATE *state, int tok,
                                   const char *ptr, const char *end,
                                   const ENCODING *enc);

static PROLOG_HANDLER prolog0_old_b026324c6904b2a, prolog1_old_b026324c6904b2a, prolog2_old_b026324c6904b2a, doctype0_old_b026324c6904b2a, doctype1_old_b026324c6904b2a, doctype2_old_b026324c6904b2a,
    doctype3_old_b026324c6904b2a, doctype4_old_b026324c6904b2a, doctype5_old_b026324c6904b2a, internalSubset_old_b026324c6904b2a, entity0_old_b026324c6904b2a, entity1_old_b026324c6904b2a, entity2_old_b026324c6904b2a,
    entity3_old_b026324c6904b2a, entity4_old_b026324c6904b2a, entity5_old_b026324c6904b2a, entity6_old_b026324c6904b2a, entity7_old_b026324c6904b2a, entity8_old_b026324c6904b2a, entity9_old_b026324c6904b2a, entity10_old_b026324c6904b2a,
    notation0_old_b026324c6904b2a, notation1_old_b026324c6904b2a, notation2_old_b026324c6904b2a, notation3_old_b026324c6904b2a, notation4_old_b026324c6904b2a, attlist0_old_b026324c6904b2a, attlist1_old_b026324c6904b2a,
    attlist2_old_b026324c6904b2a, attlist3_old_b026324c6904b2a, attlist4_old_b026324c6904b2a, attlist5_old_b026324c6904b2a, attlist6_old_b026324c6904b2a, attlist7_old_b026324c6904b2a, attlist8_old_b026324c6904b2a,
    attlist9_old_b026324c6904b2a, element0_old_b026324c6904b2a, element1_old_b026324c6904b2a, element2_old_b026324c6904b2a, element3_old_b026324c6904b2a, element4_old_b026324c6904b2a, element5_old_b026324c6904b2a,
    element6_old_b026324c6904b2a, element7_old_b026324c6904b2a,
#ifdef XML_DTD
    externalSubset0_old_b026324c6904b2a, externalSubset1_old_b026324c6904b2a, condSect0_old_b026324c6904b2a, condSect1_old_b026324c6904b2a, condSect2_old_b026324c6904b2a,
#endif /* XML_DTD */
    declClose_old_b026324c6904b2a, error_old_b026324c6904b2a;

static int FASTCALL common_old_b026324c6904b2a(PROLOG_STATE *state, int tok);

static int PTRCALL
prolog0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    state->handler = prolog1_old_b026324c6904b2a;
    return XML_ROLE_NONE;
  case XML_TOK_XML_DECL:
    state->handler = prolog1_old_b026324c6904b2a;
    return XML_ROLE_XML_DECL;
  case XML_TOK_PI:
    state->handler = prolog1_old_b026324c6904b2a;
    return XML_ROLE_PI;
  case XML_TOK_COMMENT:
    state->handler = prolog1_old_b026324c6904b2a;
    return XML_ROLE_COMMENT;
  case XML_TOK_BOM:
    return XML_ROLE_NONE;
  case XML_TOK_DECL_OPEN:
    if (! XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                              KW_DOCTYPE))
      break;
    state->handler = doctype0_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_INSTANCE_START:
    state->handler = error_old_b026324c6904b2a;
    return XML_ROLE_INSTANCE_START;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
prolog1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_PI:
    return XML_ROLE_PI;
  case XML_TOK_COMMENT:
    return XML_ROLE_COMMENT;
  case XML_TOK_BOM:
    /* This case can never arise.  To reach this role function, the
     * parse must have passed through prolog0 and therefore have had
     * some form of input, even if only a space.  At that point, a
     * byte order mark is no longer a valid character (though
     * technically it should be interpreted as a non-breaking space),
     * so will be rejected by the tokenizing stages.
     */
    return XML_ROLE_NONE; /* LCOV_EXCL_LINE */
  case XML_TOK_DECL_OPEN:
    if (! XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                              KW_DOCTYPE))
      break;
    state->handler = doctype0_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_INSTANCE_START:
    state->handler = error_old_b026324c6904b2a;
    return XML_ROLE_INSTANCE_START;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
prolog2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_PI:
    return XML_ROLE_PI;
  case XML_TOK_COMMENT:
    return XML_ROLE_COMMENT;
  case XML_TOK_INSTANCE_START:
    state->handler = error_old_b026324c6904b2a;
    return XML_ROLE_INSTANCE_START;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = doctype1_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_OPEN_BRACKET:
    state->handler = internalSubset_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_INTERNAL_SUBSET;
  case XML_TOK_DECL_CLOSE:
    state->handler = prolog2_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_CLOSE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_SYSTEM)) {
      state->handler = doctype3_old_b026324c6904b2a;
      return XML_ROLE_DOCTYPE_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_PUBLIC)) {
      state->handler = doctype2_old_b026324c6904b2a;
      return XML_ROLE_DOCTYPE_NONE;
    }
    break;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_LITERAL:
    state->handler = doctype3_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_PUBLIC_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype3_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_LITERAL:
    state->handler = doctype4_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_SYSTEM_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype4_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_OPEN_BRACKET:
    state->handler = internalSubset_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_INTERNAL_SUBSET;
  case XML_TOK_DECL_CLOSE:
    state->handler = prolog2_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_CLOSE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
doctype5_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_DECL_CLOSE:
    state->handler = prolog2_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_CLOSE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
internalSubset_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
               const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_DECL_OPEN:
    if (XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                            KW_ENTITY)) {
      state->handler = entity0_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                            KW_ATTLIST)) {
      state->handler = attlist0_old_b026324c6904b2a;
      return XML_ROLE_ATTLIST_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                            KW_ELEMENT)) {
      state->handler = element0_old_b026324c6904b2a;
      return XML_ROLE_ELEMENT_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr + 2 * MIN_BYTES_PER_CHAR(enc), end,
                            KW_NOTATION)) {
      state->handler = notation0_old_b026324c6904b2a;
      return XML_ROLE_NOTATION_NONE;
    }
    break;
  case XML_TOK_PI:
    return XML_ROLE_PI;
  case XML_TOK_COMMENT:
    return XML_ROLE_COMMENT;
  case XML_TOK_PARAM_ENTITY_REF:
    return XML_ROLE_PARAM_ENTITY_REF;
  case XML_TOK_CLOSE_BRACKET:
    state->handler = doctype5_old_b026324c6904b2a;
    return XML_ROLE_DOCTYPE_NONE;
  case XML_TOK_NONE:
    return XML_ROLE_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

#ifdef XML_DTD

static int PTRCALL
externalSubset0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
                const ENCODING *enc) {
  state->handler = externalSubset1_old_b026324c6904b2a;
  if (tok == XML_TOK_XML_DECL)
    return XML_ROLE_TEXT_DECL;
  return externalSubset1_old_b026324c6904b2a(state, tok, ptr, end, enc);
}

static int PTRCALL
externalSubset1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
                const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_COND_SECT_OPEN:
    state->handler = condSect0_old_b026324c6904b2a;
    return XML_ROLE_NONE;
  case XML_TOK_COND_SECT_CLOSE:
    if (state->includeLevel == 0)
      break;
    state->includeLevel -= 1;
    return XML_ROLE_NONE;
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_CLOSE_BRACKET:
    break;
  case XML_TOK_NONE:
    if (state->includeLevel)
      break;
    return XML_ROLE_NONE;
  default:
    return internalSubset_old_b026324c6904b2a(state, tok, ptr, end, enc);
  }
  return common_old_b026324c6904b2a(state, tok);
}

#endif /* XML_DTD */

static int PTRCALL
entity0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_PERCENT:
    state->handler = entity1_old_b026324c6904b2a;
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_NAME:
    state->handler = entity2_old_b026324c6904b2a;
    return XML_ROLE_GENERAL_ENTITY_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_NAME:
    state->handler = entity7_old_b026324c6904b2a;
    return XML_ROLE_PARAM_ENTITY_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_SYSTEM)) {
      state->handler = entity4_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_PUBLIC)) {
      state->handler = entity3_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    break;
  case XML_TOK_LITERAL:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ENTITY_NONE;
    return XML_ROLE_ENTITY_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity3_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_LITERAL:
    state->handler = entity4_old_b026324c6904b2a;
    return XML_ROLE_ENTITY_PUBLIC_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity4_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_LITERAL:
    state->handler = entity5_old_b026324c6904b2a;
    return XML_ROLE_ENTITY_SYSTEM_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity5_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_DECL_CLOSE:
    setTopLevel(state);
    return XML_ROLE_ENTITY_COMPLETE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_NDATA)) {
      state->handler = entity6_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    break;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity6_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_NAME:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ENTITY_NONE;
    return XML_ROLE_ENTITY_NOTATION_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity7_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_SYSTEM)) {
      state->handler = entity9_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_PUBLIC)) {
      state->handler = entity8_old_b026324c6904b2a;
      return XML_ROLE_ENTITY_NONE;
    }
    break;
  case XML_TOK_LITERAL:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ENTITY_NONE;
    return XML_ROLE_ENTITY_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity8_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_LITERAL:
    state->handler = entity9_old_b026324c6904b2a;
    return XML_ROLE_ENTITY_PUBLIC_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity9_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
        const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_LITERAL:
    state->handler = entity10_old_b026324c6904b2a;
    return XML_ROLE_ENTITY_SYSTEM_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
entity10_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ENTITY_NONE;
  case XML_TOK_DECL_CLOSE:
    setTopLevel(state);
    return XML_ROLE_ENTITY_COMPLETE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
notation0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NOTATION_NONE;
  case XML_TOK_NAME:
    state->handler = notation1_old_b026324c6904b2a;
    return XML_ROLE_NOTATION_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
notation1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NOTATION_NONE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_SYSTEM)) {
      state->handler = notation3_old_b026324c6904b2a;
      return XML_ROLE_NOTATION_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_PUBLIC)) {
      state->handler = notation2_old_b026324c6904b2a;
      return XML_ROLE_NOTATION_NONE;
    }
    break;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
notation2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NOTATION_NONE;
  case XML_TOK_LITERAL:
    state->handler = notation4_old_b026324c6904b2a;
    return XML_ROLE_NOTATION_PUBLIC_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
notation3_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NOTATION_NONE;
  case XML_TOK_LITERAL:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_NOTATION_NONE;
    return XML_ROLE_NOTATION_SYSTEM_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
notation4_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NOTATION_NONE;
  case XML_TOK_LITERAL:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_NOTATION_NONE;
    return XML_ROLE_NOTATION_SYSTEM_ID;
  case XML_TOK_DECL_CLOSE:
    setTopLevel(state);
    return XML_ROLE_NOTATION_NO_SYSTEM_ID;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = attlist1_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_ELEMENT_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_DECL_CLOSE:
    setTopLevel(state);
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = attlist2_old_b026324c6904b2a;
    return XML_ROLE_ATTRIBUTE_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_NAME: {
    static const char *const types[] = {
        KW_CDATA,  KW_ID,       KW_IDREF,   KW_IDREFS,
        KW_ENTITY, KW_ENTITIES, KW_NMTOKEN, KW_NMTOKENS,
    };
    int i;
    for (i = 0; i < (int)(sizeof(types) / sizeof(types[0])); i++)
      if (XmlNameMatchesAscii(enc, ptr, end, types[i])) {
        state->handler = attlist8_old_b026324c6904b2a;
        return XML_ROLE_ATTRIBUTE_TYPE_CDATA + i;
      }
  }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_NOTATION)) {
      state->handler = attlist5_old_b026324c6904b2a;
      return XML_ROLE_ATTLIST_NONE;
    }
    break;
  case XML_TOK_OPEN_PAREN:
    state->handler = attlist3_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist3_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_NMTOKEN:
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = attlist4_old_b026324c6904b2a;
    return XML_ROLE_ATTRIBUTE_ENUM_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist4_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_CLOSE_PAREN:
    state->handler = attlist8_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_OR:
    state->handler = attlist3_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist5_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_OPEN_PAREN:
    state->handler = attlist6_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist6_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_NAME:
    state->handler = attlist7_old_b026324c6904b2a;
    return XML_ROLE_ATTRIBUTE_NOTATION_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist7_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_CLOSE_PAREN:
    state->handler = attlist8_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_OR:
    state->handler = attlist6_old_b026324c6904b2a;
    return XML_ROLE_ATTLIST_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

/* default value */
static int PTRCALL
attlist8_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_POUND_NAME:
    if (XmlNameMatchesAscii(enc, ptr + MIN_BYTES_PER_CHAR(enc), end,
                            KW_IMPLIED)) {
      state->handler = attlist1_old_b026324c6904b2a;
      return XML_ROLE_IMPLIED_ATTRIBUTE_VALUE;
    }
    if (XmlNameMatchesAscii(enc, ptr + MIN_BYTES_PER_CHAR(enc), end,
                            KW_REQUIRED)) {
      state->handler = attlist1_old_b026324c6904b2a;
      return XML_ROLE_REQUIRED_ATTRIBUTE_VALUE;
    }
    if (XmlNameMatchesAscii(enc, ptr + MIN_BYTES_PER_CHAR(enc), end,
                            KW_FIXED)) {
      state->handler = attlist9_old_b026324c6904b2a;
      return XML_ROLE_ATTLIST_NONE;
    }
    break;
  case XML_TOK_LITERAL:
    state->handler = attlist1_old_b026324c6904b2a;
    return XML_ROLE_DEFAULT_ATTRIBUTE_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
attlist9_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ATTLIST_NONE;
  case XML_TOK_LITERAL:
    state->handler = attlist1_old_b026324c6904b2a;
    return XML_ROLE_FIXED_ATTRIBUTE_VALUE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = element1_old_b026324c6904b2a;
    return XML_ROLE_ELEMENT_NAME;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_EMPTY)) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
      return XML_ROLE_CONTENT_EMPTY;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_ANY)) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
      return XML_ROLE_CONTENT_ANY;
    }
    break;
  case XML_TOK_OPEN_PAREN:
    state->handler = element2_old_b026324c6904b2a;
    state->level = 1;
    return XML_ROLE_GROUP_OPEN;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_POUND_NAME:
    if (XmlNameMatchesAscii(enc, ptr + MIN_BYTES_PER_CHAR(enc), end,
                            KW_PCDATA)) {
      state->handler = element3_old_b026324c6904b2a;
      return XML_ROLE_CONTENT_PCDATA;
    }
    break;
  case XML_TOK_OPEN_PAREN:
    state->level = 2;
    state->handler = element6_old_b026324c6904b2a;
    return XML_ROLE_GROUP_OPEN;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT;
  case XML_TOK_NAME_QUESTION:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_OPT;
  case XML_TOK_NAME_ASTERISK:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_REP;
  case XML_TOK_NAME_PLUS:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_PLUS;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element3_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_CLOSE_PAREN:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ELEMENT_NONE;
    return XML_ROLE_GROUP_CLOSE;
  case XML_TOK_CLOSE_PAREN_ASTERISK:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ELEMENT_NONE;
    return XML_ROLE_GROUP_CLOSE_REP;
  case XML_TOK_OR:
    state->handler = element4_old_b026324c6904b2a;
    return XML_ROLE_ELEMENT_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element4_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = element5_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element5_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_CLOSE_PAREN_ASTERISK:
    state->handler = declClose_old_b026324c6904b2a;
    state->role_none = XML_ROLE_ELEMENT_NONE;
    return XML_ROLE_GROUP_CLOSE_REP;
  case XML_TOK_OR:
    state->handler = element4_old_b026324c6904b2a;
    return XML_ROLE_ELEMENT_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element6_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_OPEN_PAREN:
    state->level += 1;
    return XML_ROLE_GROUP_OPEN;
  case XML_TOK_NAME:
  case XML_TOK_PREFIXED_NAME:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT;
  case XML_TOK_NAME_QUESTION:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_OPT;
  case XML_TOK_NAME_ASTERISK:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_REP;
  case XML_TOK_NAME_PLUS:
    state->handler = element7_old_b026324c6904b2a;
    return XML_ROLE_CONTENT_ELEMENT_PLUS;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
element7_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
         const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_ELEMENT_NONE;
  case XML_TOK_CLOSE_PAREN:
    state->level -= 1;
    if (state->level == 0) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
    }
    return XML_ROLE_GROUP_CLOSE;
  case XML_TOK_CLOSE_PAREN_ASTERISK:
    state->level -= 1;
    if (state->level == 0) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
    }
    return XML_ROLE_GROUP_CLOSE_REP;
  case XML_TOK_CLOSE_PAREN_QUESTION:
    state->level -= 1;
    if (state->level == 0) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
    }
    return XML_ROLE_GROUP_CLOSE_OPT;
  case XML_TOK_CLOSE_PAREN_PLUS:
    state->level -= 1;
    if (state->level == 0) {
      state->handler = declClose_old_b026324c6904b2a;
      state->role_none = XML_ROLE_ELEMENT_NONE;
    }
    return XML_ROLE_GROUP_CLOSE_PLUS;
  case XML_TOK_COMMA:
    state->handler = element6_old_b026324c6904b2a;
    return XML_ROLE_GROUP_SEQUENCE;
  case XML_TOK_OR:
    state->handler = element6_old_b026324c6904b2a;
    return XML_ROLE_GROUP_CHOICE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

#ifdef XML_DTD

static int PTRCALL
condSect0_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_NAME:
    if (XmlNameMatchesAscii(enc, ptr, end, KW_INCLUDE)) {
      state->handler = condSect1_old_b026324c6904b2a;
      return XML_ROLE_NONE;
    }
    if (XmlNameMatchesAscii(enc, ptr, end, KW_IGNORE)) {
      state->handler = condSect2_old_b026324c6904b2a;
      return XML_ROLE_NONE;
    }
    break;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
condSect1_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_OPEN_BRACKET:
    state->handler = externalSubset1_old_b026324c6904b2a;
    state->includeLevel += 1;
    return XML_ROLE_NONE;
  }
  return common_old_b026324c6904b2a(state, tok);
}

static int PTRCALL
condSect2_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return XML_ROLE_NONE;
  case XML_TOK_OPEN_BRACKET:
    state->handler = externalSubset1_old_b026324c6904b2a;
    return XML_ROLE_IGNORE_SECT;
  }
  return common_old_b026324c6904b2a(state, tok);
}

#endif /* XML_DTD */

static int PTRCALL
declClose_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
          const ENCODING *enc) {
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  switch (tok) {
  case XML_TOK_PROLOG_S:
    return state->role_none;
  case XML_TOK_DECL_CLOSE:
    setTopLevel(state);
    return state->role_none;
  }
  return common_old_b026324c6904b2a(state, tok);
}

/* This function will only be invoked if the internal logic of the
 * parser has broken down.  It is used in two cases:
 *
 * 1: When the XML prolog has been finished.  At this point the
 * processor (the parser level above these role handlers) should
 * switch from prologProcessor to contentProcessor and reinitialise
 * the handler function.
 *
 * 2: When an error has been detected (via common() below).  At this
 * point again the processor should be switched to errorProcessor,
 * which will never call a handler.
 *
 * The result of this is that error() can only be called if the
 * processor switch failed to happen, which is an internal error and
 * therefore we shouldn't be able to provoke it simply by using the
 * library.  It is a necessary backstop, however, so we merely exclude
 * it from the coverage statistics.
 *
 * LCOV_EXCL_START
 */
static int PTRCALL
error_old_b026324c6904b2a(PROLOG_STATE *state, int tok, const char *ptr, const char *end,
      const ENCODING *enc) {
  UNUSED_P(state);
  UNUSED_P(tok);
  UNUSED_P(ptr);
  UNUSED_P(end);
  UNUSED_P(enc);
  return XML_ROLE_NONE;
}
/* LCOV_EXCL_STOP */

static int FASTCALL
common_old_b026324c6904b2a(PROLOG_STATE *state, int tok) {
#ifdef XML_DTD
  if (! state->documentEntity && tok == XML_TOK_PARAM_ENTITY_REF)
    return XML_ROLE_INNER_PARAM_ENTITY_REF;
#else
  UNUSED_P(tok);
#endif
  state->handler = error_old_b026324c6904b2a;
  return XML_ROLE_ERROR;
}

void
XmlPrologStateInit_old_b026324c6904b2a(PROLOG_STATE *state) {
  state->handler = prolog0_old_b026324c6904b2a;
#ifdef XML_DTD
  state->documentEntity = 1;
  state->includeLevel = 0;
  state->inEntityValue = 0;
#endif /* XML_DTD */
}

#ifdef XML_DTD

void
XmlPrologStateInitExternalEntity_old_b026324c6904b2a(PROLOG_STATE *state) {
  state->handler = externalSubset0_old_b026324c6904b2a;
  state->documentEntity = 0;
  state->includeLevel = 0;
}

#endif /* XML_DTD */
