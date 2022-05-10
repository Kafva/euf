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

/* Added as a requirement for sizeof(struct XML_ParserStruct) 
 * in .e.g. lib/xmlparse.c:5763:1:defineAttribute() */
struct XML_ParserStruct {
  /* The first member must be m_userData so that the XML_GetUserData
     macro works. */
  void *m_userData;
  void *m_handlerArg;
  char *m_buffer;
  const XML_Memory_Handling_Suite m_mem;
  /* first character to be parsed */
  const char *m_bufferPtr;
  /* past last character to be parsed */
  char *m_bufferEnd;
  /* allocated end of m_buffer */
  const char *m_bufferLim;
  XML_Index m_parseEndByteIndex;
  const char *m_parseEndPtr;
  XML_Char *m_dataBuf;
  XML_Char *m_dataBufEnd;
  XML_StartElementHandler m_startElementHandler;
  XML_EndElementHandler m_endElementHandler;
  XML_CharacterDataHandler m_characterDataHandler;
  XML_ProcessingInstructionHandler m_processingInstructionHandler;
  XML_CommentHandler m_commentHandler;
  XML_StartCdataSectionHandler m_startCdataSectionHandler;
  XML_EndCdataSectionHandler m_endCdataSectionHandler;
  XML_DefaultHandler m_defaultHandler;
  XML_StartDoctypeDeclHandler m_startDoctypeDeclHandler;
  XML_EndDoctypeDeclHandler m_endDoctypeDeclHandler;
  XML_UnparsedEntityDeclHandler m_unparsedEntityDeclHandler;
  XML_NotationDeclHandler m_notationDeclHandler;
  XML_StartNamespaceDeclHandler m_startNamespaceDeclHandler;
  XML_EndNamespaceDeclHandler m_endNamespaceDeclHandler;
  XML_NotStandaloneHandler m_notStandaloneHandler;
  XML_ExternalEntityRefHandler m_externalEntityRefHandler;
  XML_Parser m_externalEntityRefHandlerArg;
  XML_SkippedEntityHandler m_skippedEntityHandler;
  XML_UnknownEncodingHandler m_unknownEncodingHandler;
  XML_ElementDeclHandler m_elementDeclHandler;
  XML_AttlistDeclHandler m_attlistDeclHandler;
  XML_EntityDeclHandler m_entityDeclHandler;
  XML_XmlDeclHandler m_xmlDeclHandler;
  const ENCODING *m_encoding;
  INIT_ENCODING m_initEncoding;
  const ENCODING *m_internalEncoding;
  const XML_Char *m_protocolEncodingName;
  XML_Bool m_ns;
  XML_Bool m_ns_triplets;
  void *m_unknownEncodingMem;
  void *m_unknownEncodingData;
  void *m_unknownEncodingHandlerData;
  void(XMLCALL *m_unknownEncodingRelease)(void *);
  PROLOG_STATE m_prologState;
  Processor *m_processor;
  enum XML_Error m_errorCode;
  const char *m_eventPtr;
  const char *m_eventEndPtr;
  const char *m_positionPtr;
  OPEN_INTERNAL_ENTITY *m_openInternalEntities;
  OPEN_INTERNAL_ENTITY *m_freeInternalEntities;
  XML_Bool m_defaultExpandInternalEntities;
  int m_tagLevel;
  ENTITY *m_declEntity;
  const XML_Char *m_doctypeName;
  const XML_Char *m_doctypeSysid;
  const XML_Char *m_doctypePubid;
  const XML_Char *m_declAttributeType;
  const XML_Char *m_declNotationName;
  const XML_Char *m_declNotationPublicId;
  ELEMENT_TYPE *m_declElementType;
  ATTRIBUTE_ID *m_declAttributeId;
  XML_Bool m_declAttributeIsCdata;
  XML_Bool m_declAttributeIsId;
  DTD *m_dtd;
  const XML_Char *m_curBase;
  TAG *m_tagStack;
  TAG *m_freeTagList;
  BINDING *m_inheritedBindings;
  BINDING *m_freeBindingList;
  int m_attsSize;
  int m_nSpecifiedAtts;
  int m_idAttIndex;
  ATTRIBUTE *m_atts;
  NS_ATT *m_nsAtts;
  unsigned long m_nsAttsVersion;
  unsigned char m_nsAttsPower;
#ifdef XML_ATTR_INFO
  XML_AttrInfo *m_attInfo;
#endif
  POSITION m_position;
  STRING_POOL m_tempPool;
  STRING_POOL m_temp2Pool;
  char *m_groupConnector;
  unsigned int m_groupSize;
  XML_Char m_namespaceSeparator;
  XML_Parser m_parentParser;
  XML_ParsingStatus m_parsingStatus;
#ifdef XML_DTD
  XML_Bool m_isParamEntity;
  XML_Bool m_useForeignDTD;
  enum XML_ParamEntityParsing m_paramEntityParsing;
#endif
  unsigned long m_hash_secret_salt;
};

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
