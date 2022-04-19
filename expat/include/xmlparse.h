/* 69df5be70289a11fb834869ce4a91c23c1d9dd04baffcbd10e86742d149a080c (2.2.7+)
                            __  __            _
                         ___\ \/ /_ __   __ _| |_
                        / _ \\  /| '_ \ / _` | __|
                       |  __//  \| |_) | (_| | |_
                        \___/_/\_\ .__/ \__,_|\__|
                                 |_| XML parser

   Copyright (c) 1997-2000 Thai Open Source Software Center Ltd
   Copyright (c) 2000-2017 Expat development team
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

#if ! defined(_GNU_SOURCE)
#  define _GNU_SOURCE 1 /* syscall prototype */
#endif

#ifdef _WIN32
/* force stdlib to define rand_s() */
#  define _CRT_RAND_S
#endif

#include <stddef.h>
#include <string.h> /* memset(), memcpy() */
#include <assert.h>
#include <limits.h> /* UINT_MAX */
#include <stdio.h>  /* fprintf */
#include <stdlib.h> /* getenv, rand_s */

#ifdef _WIN32
#  define getpid GetCurrentProcessId
#else
#  include <sys/time.h>  /* gettimeofday() */
#  include <sys/types.h> /* getpid() */
#  include <unistd.h>    /* getpid() */
#  include <fcntl.h>     /* O_RDONLY */
#  include <errno.h>
#endif

#define XML_BUILDING_EXPAT 1

#ifdef _WIN32
#  include "winconfig.h"
#elif defined(HAVE_EXPAT_CONFIG_H)
#  include <expat_config.h>
#endif /* ndef _WIN32 */

#include "ascii.h"
#include "expat.h"
#include "siphash.h"

#if defined(HAVE_GETRANDOM) || defined(HAVE_SYSCALL_GETRANDOM)
#  if defined(HAVE_GETRANDOM)
#    include <sys/random.h> /* getrandom */
#  else
#    include <unistd.h>      /* syscall */
#    include <sys/syscall.h> /* SYS_getrandom */
#  endif
#  if ! defined(GRND_NONBLOCK)
#    define GRND_NONBLOCK 0x0001
#  endif /* defined(GRND_NONBLOCK) */
#endif   /* defined(HAVE_GETRANDOM) || defined(HAVE_SYSCALL_GETRANDOM) */

#if defined(HAVE_LIBBSD)                                                       \
    && (defined(HAVE_ARC4RANDOM_BUF) || defined(HAVE_ARC4RANDOM))
#  include <bsd/stdlib.h>
#endif

#if defined(_WIN32) && ! defined(LOAD_LIBRARY_SEARCH_SYSTEM32)
#  define LOAD_LIBRARY_SEARCH_SYSTEM32 0x00000800
#endif

#if ! defined(HAVE_GETRANDOM) && ! defined(HAVE_SYSCALL_GETRANDOM)             \
    && ! defined(HAVE_ARC4RANDOM_BUF) && ! defined(HAVE_ARC4RANDOM)            \
    && ! defined(XML_DEV_URANDOM) && ! defined(_WIN32)                         \
    && ! defined(XML_POOR_ENTROPY)
#  error You do not have support for any sources of high quality entropy \
    enabled.  For end user security, that is probably not what you want. \
    \
    Your options include: \
      * Linux + glibc >=2.25 (getrandom): HAVE_GETRANDOM, \
      * Linux + glibc <2.25 (syscall SYS_getrandom): HAVE_SYSCALL_GETRANDOM, \
      * BSD / macOS >=10.7 (arc4random_buf): HAVE_ARC4RANDOM_BUF, \
      * BSD / macOS <10.7 (arc4random): HAVE_ARC4RANDOM, \
      * libbsd (arc4random_buf): HAVE_ARC4RANDOM_BUF + HAVE_LIBBSD, \
      * libbsd (arc4random): HAVE_ARC4RANDOM + HAVE_LIBBSD, \
      * Linux / BSD / macOS (/dev/urandom): XML_DEV_URANDOM \
      * Windows (rand_s): _WIN32. \
    \
    If insist on not using any of these, bypass this error by defining \
    XML_POOR_ENTROPY; you have been warned. \
    \
    If you have reasons to patch this detection code away or need changes \
    to the build system, please open a bug.  Thank you!
#endif

#ifdef XML_UNICODE
#  define XML_ENCODE_MAX XML_UTF16_ENCODE_MAX
#  define XmlConvert XmlUtf16Convert
#  define XmlGetInternalEncoding XmlGetUtf16InternalEncoding
#  define XmlGetInternalEncodingNS XmlGetUtf16InternalEncodingNS
#  define XmlEncode XmlUtf16Encode
/* Using pointer subtraction to convert to integer type. */
#  define MUST_CONVERT(enc, s)                                                 \
    (! (enc)->isUtf16 || (((char *)(s) - (char *)NULL) & 1))
typedef unsigned short ICHAR;
#else
#  define XML_ENCODE_MAX XML_UTF8_ENCODE_MAX
#  define XmlConvert XmlUtf8Convert
#  define XmlGetInternalEncoding XmlGetUtf8InternalEncoding
#  define XmlGetInternalEncodingNS XmlGetUtf8InternalEncodingNS
#  define XmlEncode XmlUtf8Encode
#  define MUST_CONVERT(enc, s) (! (enc)->isUtf8)
typedef char ICHAR;
#endif

#ifndef XML_NS

#  define XmlInitEncodingNS XmlInitEncoding
#  define XmlInitUnknownEncodingNS XmlInitUnknownEncoding
#  undef XmlGetInternalEncodingNS
#  define XmlGetInternalEncodingNS XmlGetInternalEncoding
#  define XmlParseXmlDeclNS XmlParseXmlDecl

#endif

#ifdef XML_UNICODE

#  ifdef XML_UNICODE_WCHAR_T
#    define XML_T(x) (const wchar_t) x
#    define XML_L(x) L##x
#  else
#    define XML_T(x) (const unsigned short)x
#    define XML_L(x) x
#  endif

#else

#  define XML_T(x) x
#  define XML_L(x) x

#endif

/* Round up n to be a multiple of sz, where sz is a power of 2. */
#define ROUND_UP(n, sz) (((n) + ((sz)-1)) & ~((sz)-1))

/* Do safe (NULL-aware) pointer arithmetic */
#define EXPAT_SAFE_PTR_DIFF(p, q) (((p) && (q)) ? ((p) - (q)) : 0)

#include "internal.h"
#include "xmltok.h"
#include "xmlrole.h"

typedef const XML_Char *KEY;

typedef struct {
  KEY name;
} NAMED;

typedef struct {
  NAMED **v;
  unsigned char power;
  size_t size;
  size_t used;
  const XML_Memory_Handling_Suite *mem;
} HASH_TABLE;

 size_t keylen(KEY s);

 void copy_salt_to_sipkey(XML_Parser parser, struct sipkey *key);

/* For probing (after a collision) we need a step size relative prime
   to the hash table size, which is a power of 2. We use double-hashing,
   since we can calculate a second hash value cheaply by taking those bits
   of the first hash value that were discarded (masked out) when the table
   index was calculated: index = hash & mask, where mask = table->size - 1.
   We limit the maximum step size to table->size / 4 (mask >> 2) and make
   it odd, since odd numbers are always relative prime to a power of 2.
*/
#define SECOND_HASH(hash, mask, power)                                         \
  ((((hash) & ~(mask)) >> ((power)-1)) & ((mask) >> 2))
#define PROBE_STEP(hash, mask, power)                                          \
  ((unsigned char)((SECOND_HASH(hash, mask, power)) | 1))

typedef struct {
  NAMED **p;
  NAMED **end;
} HASH_TABLE_ITER;

#define INIT_TAG_BUF_SIZE 32 /* must be a multiple of sizeof(XML_Char) */
#define INIT_DATA_BUF_SIZE 1024
#define INIT_ATTS_SIZE 16
#define INIT_ATTS_VERSION 0xFFFFFFFF
#define INIT_BLOCK_SIZE 1024
#define INIT_BUFFER_SIZE 1024

#define EXPAND_SPARE 24

typedef struct binding {
  struct prefix *prefix;
  struct binding *nextTagBinding;
  struct binding *prevPrefixBinding;
  const struct attribute_id *attId;
  XML_Char *uri;
  int uriLen;
  int uriAlloc;
} BINDING;

typedef struct prefix {
  const XML_Char *name;
  BINDING *binding;
} PREFIX;

typedef struct {
  const XML_Char *str;
  const XML_Char *localPart;
  const XML_Char *prefix;
  int strLen;
  int uriLen;
  int prefixLen;
} TAG_NAME;

/* TAG represents an open element.
   The name of the element is stored in both the document and API
   encodings.  The memory buffer 'buf' is a separately-allocated
   memory area which stores the name.  During the XML_Parse()/
   XMLParseBuffer() when the element is open, the memory for the 'raw'
   version of the name (in the document encoding) is shared with the
   document buffer.  If the element is open across calls to
   XML_Parse()/XML_ParseBuffer(), the buffer is re-allocated to
   contain the 'raw' name as well.

   A parser re-uses these structures, maintaining a list of allocated
   TAG objects in a free list.
*/
typedef struct tag {
  struct tag *parent;  /* parent of this element */
  const char *rawName; /* tagName in the original encoding */
  int rawNameLength;
  TAG_NAME name; /* tagName in the API encoding */
  char *buf;     /* buffer for name components */
  char *bufEnd;  /* end of the buffer */
  BINDING *bindings;
} TAG;

typedef struct {
  const XML_Char *name;
  const XML_Char *textPtr;
  int textLen;   /* length in XML_Chars */
  int processed; /* # of processed bytes - when suspended */
  const XML_Char *systemId;
  const XML_Char *base;
  const XML_Char *publicId;
  const XML_Char *notation;
  XML_Bool open;
  XML_Bool is_param;
  XML_Bool is_internal; /* true if declared in internal subset outside PE */
} ENTITY;

typedef struct {
  enum XML_Content_Type type;
  enum XML_Content_Quant quant;
  const XML_Char *name;
  int firstchild;
  int lastchild;
  int childcnt;
  int nextsib;
} CONTENT_SCAFFOLD;

#define INIT_SCAFFOLD_ELEMENTS 32

typedef struct block {
  struct block *next;
  int size;
  XML_Char s[1];
} BLOCK;

typedef struct {
  BLOCK *blocks;
  BLOCK *freeBlocks;
  const XML_Char *end;
  XML_Char *ptr;
  XML_Char *start;
  const XML_Memory_Handling_Suite *mem;
} STRING_POOL;

/* The XML_Char before the name is used to determine whether
   an attribute has been specified. */
typedef struct attribute_id {
  XML_Char *name;
  PREFIX *prefix;
  XML_Bool maybeTokenized;
  XML_Bool xmlns;
} ATTRIBUTE_ID;

typedef struct {
  const ATTRIBUTE_ID *id;
  XML_Bool isCdata;
  const XML_Char *value;
} DEFAULT_ATTRIBUTE;

typedef struct {
  unsigned long version;
  unsigned long hash;
  const XML_Char *uriName;
} NS_ATT;

typedef struct {
  const XML_Char *name;
  PREFIX *prefix;
  const ATTRIBUTE_ID *idAtt;
  int nDefaultAtts;
  int allocDefaultAtts;
  DEFAULT_ATTRIBUTE *defaultAtts;
} ELEMENT_TYPE;

typedef struct {
  HASH_TABLE generalEntities;
  HASH_TABLE elementTypes;
  HASH_TABLE attributeIds;
  HASH_TABLE prefixes;
  STRING_POOL pool;
  STRING_POOL entityValuePool;
  /* false once a parameter entity reference has been skipped */
  XML_Bool keepProcessing;
  /* true once an internal or external PE reference has been encountered;
     this includes the reference to an external subset */
  XML_Bool hasParamEntityRefs;
  XML_Bool standalone;
#ifdef XML_DTD
  /* indicates if external PE has been read */
  XML_Bool paramEntityRead;
  HASH_TABLE paramEntities;
#endif /* XML_DTD */
  PREFIX defaultPrefix;
  /* === scaffolding for building content model === */
  XML_Bool in_eldecl;
  CONTENT_SCAFFOLD *scaffold;
  unsigned contentStringLen;
  unsigned scaffSize;
  unsigned scaffCount;
  int scaffLevel;
  int *scaffIndex;
} DTD;

typedef struct open_internal_entity {
  const char *internalEventPtr;
  const char *internalEventEndPtr;
  struct open_internal_entity *next;
  ENTITY *entity;
  int startTagLevel;
  XML_Bool betweenDecl; /* WFC: PE Between Declarations */
} OPEN_INTERNAL_ENTITY;

typedef enum XML_Error PTRCALL Processor(XML_Parser parser, const char *start,
                                         const char *end, const char **endPtr);


 Processor prologProcessor;
 Processor prologInitProcessor;
 Processor contentProcessor;
 Processor cdataSectionProcessor;
#ifdef XML_DTD
 Processor ignoreSectionProcessor;
 Processor externalParEntProcessor;
 Processor externalParEntInitProcessor;
 Processor entityValueProcessor;
 Processor entityValueInitProcessor;
#endif /* XML_DTD */
 Processor epilogProcessor;
 Processor errorProcessor;
 Processor externalEntityInitProcessor;
 Processor externalEntityInitProcessor2;
 Processor externalEntityInitProcessor3;
 Processor externalEntityContentProcessor;
 Processor internalEntityProcessor;

 enum XML_Error handleUnknownEncoding(XML_Parser parser,
                                            const XML_Char *encodingName);
 enum XML_Error processXmlDecl(XML_Parser parser, int isGeneralTextEntity,
                                     const char *s, const char *next);
 enum XML_Error initializeEncoding(XML_Parser parser);
 enum XML_Error doProlog(XML_Parser parser, const ENCODING *enc,
                               const char *s, const char *end, int tok,
                               const char *next, const char **nextPtr,
                               XML_Bool haveMore);
 enum XML_Error processInternalEntity(XML_Parser parser, ENTITY *entity,
                                            XML_Bool betweenDecl);
 enum XML_Error doContent(XML_Parser parser, int startTagLevel,
                                const ENCODING *enc, const char *start,
                                const char *end, const char **endPtr,
                                XML_Bool haveMore);
 enum XML_Error doCdataSection(XML_Parser parser, const ENCODING *,
                                     const char **startPtr, const char *end,
                                     const char **nextPtr, XML_Bool haveMore);
#ifdef XML_DTD
 enum XML_Error doIgnoreSection(XML_Parser parser, const ENCODING *,
                                      const char **startPtr, const char *end,
                                      const char **nextPtr, XML_Bool haveMore);
#endif /* XML_DTD */

 void freeBindings(XML_Parser parser, BINDING *bindings);
 enum XML_Error storeAtts(XML_Parser parser, const ENCODING *,
                                const char *s, TAG_NAME *tagNamePtr,
                                BINDING **bindingsPtr);
 enum XML_Error addBinding(XML_Parser parser, PREFIX *prefix,
                                 const ATTRIBUTE_ID *attId, const XML_Char *uri,
                                 BINDING **bindingsPtr);
 int defineAttribute(ELEMENT_TYPE *type, ATTRIBUTE_ID *, XML_Bool isCdata,
                           XML_Bool isId, const XML_Char *dfltValue,
                           XML_Parser parser);
 enum XML_Error storeAttributeValue(XML_Parser parser, const ENCODING *,
                                          XML_Bool isCdata, const char *,
                                          const char *, STRING_POOL *);
 enum XML_Error appendAttributeValue(XML_Parser parser, const ENCODING *,
                                           XML_Bool isCdata, const char *,
                                           const char *, STRING_POOL *);
