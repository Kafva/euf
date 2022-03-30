#include <assert.h>
#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef NULL
#define NULL ((void*)0)
#endif

// tag-#anon#ST[*{*{SYM#0={ST[*{cS8}$cS8$'name']}}$SYM#0$}$*{SYM#0}$SYM#0$$'p'|*{*{SYM#0}$SYM#0$}$*{SYM#0}$SYM#0$$'end']
// file xmlparse.c line 232
struct anonymous$6;

// tag-#anon#ST[*{*{SYM#0={ST[*{cS8}$cS8$'name']}}$SYM#0$}$*{SYM#0}$SYM#0$$'v'|U8'power'|U56'$pad2'|U64'size'|U64'used'|*{cSYM#1={ST[*{*{V}$V$(U64)->*{V}$V$}$*{V}$V$(U64)->*{V}$V$$'malloc_fcn'|*{*{V}$V$(*{V}$V$|U64)->*{V}$V$}$*{V}$V$(*{V}$V$|U64)->*{V}$V$$'realloc_fcn'|*{V(*{V}$V$)->V}$V(*{V}$V$)->V$'free_fcn']}}$cSYM#1$'mem']
// file xmlparse.c line 207
struct anonymous$5;

// tag-#anon#ST[*{*{V}$V$(U64)->*{V}$V$}$*{V}$V$(U64)->*{V}$V$$'malloc_fcn'|*{*{V}$V$(*{V}$V$|U64)->*{V}$V$}$*{V}$V$(*{V}$V$|U64)->*{V}$V$$'realloc_fcn'|*{V(*{V}$V$)->V}$V(*{V}$V$)->V$'free_fcn']
// file expat.h line 218
struct anonymous$4;

// tag-#anon#ST[*{SYMblock#0={ST[*{SYMblock#0}$SYMblock#0$'next'|S32'size'|ARR1{S8}$S8$'s'|U24'$pad3']}}$SYMblock#0$'blocks'|*{SYMblock#0}$SYMblock#0$'freeBlocks'|*{cS8}$cS8$'end'|*{S8}$S8$'ptr'|*{S8}$S8$'start'|*{cSYM#1={ST[*{*{V}$V$(U64)->*{V}$V$}$*{V}$V$(U64)->*{V}$V$$'malloc_fcn'|*{*{V}$V$(*{V}$V$|U64)->*{V}$V$}$*{V}$V$(*{V}$V$|U64)->*{V}$V$$'realloc_fcn'|*{V(*{V}$V$)->V}$V(*{V}$V$)->V$'free_fcn']}}$cSYM#1$'mem']
// file xmlparse.c line 325
struct anonymous$0;

// tag-#anon#ST[*{cS8}$cS8$'name']
// file xmlparse.c line 203
struct anonymous$7;

// tag-#anon#ST[*{cS8}$cS8$'name'|*{SYMprefix#0={ST[*{cS8}$cS8$'name'|*{SYMbinding#1={ST[*{SYMprefix#0}$SYMprefix#0$'prefix'|*{SYMbinding#1}$SYMbinding#1$'nextTagBinding'|*{SYMbinding#1}$SYMbinding#1$'prevPrefixBinding'|*{cSYMattribute_id#2={ST[*{S8}$S8$'name'|*{SYMprefix#0}$SYMprefix#0$'prefix'|U8'maybeTokenized'|U8'xmlns'|U48'$pad4']}}$cSYMattribute_id#2$'attId'|*{S8}$S8$'uri'|S32'uriLen'|S32'uriAlloc']}}$SYMbinding#1$'binding']}}$SYMprefix#0$'prefix'|*{cSYMattribute_id#2}$cSYMattribute_id#2$'idAtt'|S32'nDefaultAtts'|S32'allocDefaultAtts'|*{SYM#3={ST[*{cSYMattribute_id#2}$cSYMattribute_id#2$'id'|U8'isCdata'|U56'$pad2'|*{cS8}$cS8$'value']}}$SYM#3$'defaultAtts']
// file xmlparse.c line 355
struct anonymous$10;

// tag-#anon#ST[*{cS8}$cS8$'name'|*{cS8}$cS8$'textPtr'|S32'textLen'|S32'processed'|*{cS8}$cS8$'systemId'|*{cS8}$cS8$'base'|*{cS8}$cS8$'publicId'|*{cS8}$cS8$'notation'|U8'open'|U8'is_param'|U8'is_internal'|U40'$pad11']
// file xmlparse.c line 293
struct anonymous$3;

// tag-#anon#ST[*{cS8}$cS8$'name'|*{cS8}$cS8$'valuePtr'|*{cS8}$cS8$'valueEnd'|S8'normalized'|U56'$pad4']
// file xmltok.h line 152
struct anonymous$1;

// tag-#anon#ST[*{cS8}$cS8$'str'|*{cS8}$cS8$'localPart'|*{cS8}$cS8$'prefix'|S32'strLen'|S32'uriLen'|S32'prefixLen'|U32'$pad6']
// file xmlparse.c line 261
struct anonymous$13;

// tag-#anon#ST[*{cSYMattribute_id#0={ST[*{S8}$S8$'name'|*{SYMprefix#1={ST[*{cS8}$cS8$'name'|*{SYMbinding#2={ST[*{SYMprefix#1}$SYMprefix#1$'prefix'|*{SYMbinding#2}$SYMbinding#2$'nextTagBinding'|*{SYMbinding#2}$SYMbinding#2$'prevPrefixBinding'|*{cSYMattribute_id#0}$cSYMattribute_id#0$'attId'|*{S8}$S8$'uri'|S32'uriLen'|S32'uriAlloc']}}$SYMbinding#2$'binding']}}$SYMprefix#1$'prefix'|U8'maybeTokenized'|U8'xmlns'|U48'$pad4']}}$cSYMattribute_id#0$'id'|U8'isCdata'|U56'$pad2'|*{cS8}$cS8$'value']
// file xmlparse.c line 343
struct anonymous$12;

// tag-#anon#ST[ARR256{S32}$S32$'map'|*{V}$V$'data'|*{S32(*{V}$V$|*{cS8}$cS8$)->S32}$S32(*{V}$V$|*{cS8}$cS8$)->S32$'convert'|*{V(*{V}$V$)->V}$V(*{V}$V$)->V$'release']
// file expat.h line 507
struct anonymous$16;

// tag-#anon#ST[EN[0'XML_FEATURE_END'|1'XML_FEATURE_UNICODE'|2'XML_FEATURE_UNICODE_WCHAR_T'|3'XML_FEATURE_DTD'|4'XML_FEATURE_CONTEXT_BYTES'|5'XML_FEATURE_MIN_SIZE'|6'XML_FEATURE_SIZEOF_XML_CHAR'|7'XML_FEATURE_SIZEOF_XML_LCHAR'|8'XML_FEATURE_NS'|9'XML_FEATURE_LARGE_SIZE'|A'XML_FEATURE_ATTR_INFO'|B'XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_MAXIMUM_AMPLIFICATION_DEFAULT'|C'XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_ACTIVATION_THRESHOLD_DEFAULT'{U32}$U32$'feature'|U32'$pad1'|*{cS8}$cS8$'name'|S64'value']
// file expat.h line 1018
struct anonymous$14;

// tag-#anon#ST[EN[0'XML_INITIALIZED'|1'XML_PARSING'|2'XML_FINISHED'|3'XML_SUSPENDED'{U32}$U32$'parsing'|U8'finalBuffer'|U24'$pad2']
// file expat.h line 828
struct anonymous$15;

// tag-#anon#ST[EN[1'XML_CTYPE_EMPTY'|2'XML_CTYPE_ANY'|3'XML_CTYPE_MIXED'|4'XML_CTYPE_NAME'|5'XML_CTYPE_CHOICE'|6'XML_CTYPE_SEQ'{U32}$U32$'type'|EN[0'XML_CQUANT_NONE'|1'XML_CQUANT_OPT'|2'XML_CQUANT_REP'|3'XML_CQUANT_PLUS'{U32}$U32$'quant'|*{cS8}$cS8$'name'|S32'firstchild'|S32'lastchild'|S32'childcnt'|S32'nextsib']
// file xmlparse.c line 307
struct anonymous;

// tag-#anon#ST[S32'major'|S32'minor'|S32'micro']
// file expat.h line 987
struct anonymous$2;

// tag-#anon#ST[SYM#0={ST[*{*{SYM#1={ST[*{cS8}$cS8$'name']}}$SYM#1$}$*{SYM#1}$SYM#1$$'v'|U8'power'|U56'$pad2'|U64'size'|U64'used'|*{cSYM#2={ST[*{*{V}$V$(U64)->*{V}$V$}$*{V}$V$(U64)->*{V}$V$$'malloc_fcn'|*{*{V}$V$(*{V}$V$|U64)->*{V}$V$}$*{V}$V$(*{V}$V$|U64)->*{V}$V$$'realloc_fcn'|*{V(*{V}$V$)->V}$V(*{V}$V$)->V$'free_fcn']}}$cSYM#2$'mem']}'generalEntities'|SYM#0'elementTypes'|SYM#0'attributeIds'|SYM#0'prefixes'|SYM#3={ST[*{SYMblock#4={ST[*{SYMblock#4}$SYMblock#4$'next'|S32'size'|ARR1{S8}$S8$'s'|U24'$pad3']}}$SYMblock#4$'blocks'|*{SYMblock#4}$SYMblock#4$'freeBlocks'|*{cS8}$cS8$'end'|*{S8}$S8$'ptr'|*{S8}$S8$'start'|*{cSYM#2}$cSYM#2$'mem']}'pool'|SYM#3'entityValuePool'|U8'keepProcessing'|U8'hasParamEntityRefs'|U8'standalone'|U8'paramEntityRead'|U32'$pad10'|SYM#0'paramEntities'|SYMprefix#5={ST[*{cS8}$cS8$'name'|*{SYMbinding#6={ST[*{SYMprefix#5}$SYMprefix#5$'prefix'|*{SYMbinding#6}$SYMbinding#6$'nextTagBinding'|*{SYMbinding#6}$SYMbinding#6$'prevPrefixBinding'|*{cSYMattribute_id#7={ST[*{S8}$S8$'name'|*{SYMprefix#5}$SYMprefix#5$'prefix'|U8'maybeTokenized'|U8'xmlns'|U48'$pad4']}}$cSYMattribute_id#7$'attId'|*{S8}$S8$'uri'|S32'uriLen'|S32'uriAlloc']}}$SYMbinding#6$'binding']}'defaultPrefix'|U8'in_eldecl'|U56'$pad14'|*{SYM#8={ST[EN[1'XML_CTYPE_EMPTY'|2'XML_CTYPE_ANY'|3'XML_CTYPE_MIXED'|4'XML_CTYPE_NAME'|5'XML_CTYPE_CHOICE'|6'XML_CTYPE_SEQ'{U32}$U32$'type'|EN[0'XML_CQUANT_NONE'|1'XML_CQUANT_OPT'|2'XML_CQUANT_REP'|3'XML_CQUANT_PLUS'{U32}$U32$'quant'|*{cS8}$cS8$'name'|S32'firstchild'|S32'lastchild'|S32'childcnt'|S32'nextsib']}}$SYM#8$'scaffold'|U32'contentStringLen'|U32'scaffSize'|U32'scaffCount'|S32'scaffLevel'|*{S32}$S32$'scaffIndex']
// file xmlparse.c line 364
struct anonymous$9;

// tag-#anon#ST[SYMencoding#0={ST[ARR4{*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32$}$*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32$$'scanners'|ARR2{*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32$}$*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32$$'literalScanners'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{cS8}$cS8$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{cS8}$cS8$)->S32$'nameMatchesAscii'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->S32$'nameLength'|*{*{cS8}$cS8$(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->*{cS8}$cS8$}$*{cS8}$cS8$(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->*{cS8}$cS8$$'skipS'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|S32|*{SYM#1={ST[*{cS8}$cS8$'name'|*{cS8}$cS8$'valuePtr'|*{cS8}$cS8$'valueEnd'|S8'normalized'|U56'$pad4']}}$SYM#1$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|S32|*{SYM#1}$SYM#1$)->S32$'getAtts'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$)->S32$'charRefNumber'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$)->S32$'predefinedEntityName'|*{V(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{SYMposition#2={ST[U64'lineNumber'|U64'columnNumber']}}$SYMposition#2$)->V}$V(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{SYMposition#2}$SYMposition#2$)->V$'updatePosition'|*{S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32}$S32(*{cSYMencoding#0}$cSYMencoding#0$|*{cS8}$cS8$|*{cS8}$cS8$|*{*{cS8}$cS8$}$*{cS8}$cS8$$)->S32$'isPublicId'|*{EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$(*{cSYMencoding#0}$cSYMencoding#0$|*{*{cS8}$cS8$}$*{cS8}$cS8$$|*{cS8}$cS8$|*{*{S8}$S8$}$*{S8}$S8$$|*{cS8}$cS8$)->EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$}$EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$(*{cSYMencoding#0}$cSYMencoding#0$|*{*{cS8}$cS8$}$*{cS8}$cS8$$|*{cS8}$cS8$|*{*{S8}$S8$}$*{S8}$S8$$|*{cS8}$cS8$)->EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$$'utf8Convert'|*{EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$(*{cSYMencoding#0}$cSYMencoding#0$|*{*{cS8}$cS8$}$*{cS8}$cS8$$|*{cS8}$cS8$|*{*{U16}$U16$}$*{U16}$U16$$|*{cU16}$cU16$)->EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$}$EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$(*{cSYMencoding#0}$cSYMencoding#0$|*{*{cS8}$cS8$}$*{cS8}$cS8$$|*{cS8}$cS8$|*{*{U16}$U16$}$*{U16}$U16$$|*{cU16}$cU16$)->EN[0'XML_CONVERT_COMPLETED'|1'XML_CONVERT_INPUT_INCOMPLETE'|2'XML_CONVERT_OUTPUT_EXHAUSTED'{U32}$U32$$'utf16Convert'|S32'minBytesPerChar'|S8'isUtf8'|S8'isUtf16'|U16'$pad15']}'initEnc'|*{*{cSYMencoding#0}$cSYMencoding#0$}$*{cSYMencoding#0}$cSYMencoding#0$$'encPtr']
// file xmltok.h line 281
struct anonymous$8;

// tag-#anon#ST[U64'version'|U64'hash'|*{cS8}$cS8$'uriName']
// file xmlparse.c line 349
struct anonymous$11;

// tag-XML_Account
// file xmlparse.c line 402
enum XML_Account { XML_ACCOUNT_DIRECT=0, XML_ACCOUNT_ENTITY_EXPANSION=1, XML_ACCOUNT_NONE=2 };

// tag-XML_Content_Quant
// file expat.h line 141
enum XML_Content_Quant { XML_CQUANT_NONE=0, XML_CQUANT_OPT=1, XML_CQUANT_REP=2, XML_CQUANT_PLUS=3 };

// tag-XML_Content_Type
// file expat.h line 132
enum XML_Content_Type { XML_CTYPE_EMPTY=1, XML_CTYPE_ANY=2, XML_CTYPE_MIXED=3, XML_CTYPE_NAME=4, XML_CTYPE_CHOICE=5, XML_CTYPE_SEQ=6 };

// tag-XML_Convert_Result
// file xmltok.h line 165
enum XML_Convert_Result { XML_CONVERT_COMPLETED=0, XML_CONVERT_INPUT_INCOMPLETE=1, XML_CONVERT_OUTPUT_EXHAUSTED=2 };

// tag-XML_Error
// file expat.h line 79
enum XML_Error { XML_ERROR_NONE=0, XML_ERROR_NO_MEMORY=1, XML_ERROR_SYNTAX=2, XML_ERROR_NO_ELEMENTS=3, XML_ERROR_INVALID_TOKEN=4, XML_ERROR_UNCLOSED_TOKEN=5, XML_ERROR_PARTIAL_CHAR=6, XML_ERROR_TAG_MISMATCH=7, XML_ERROR_DUPLICATE_ATTRIBUTE=8, XML_ERROR_JUNK_AFTER_DOC_ELEMENT=9, XML_ERROR_PARAM_ENTITY_REF=10, XML_ERROR_UNDEFINED_ENTITY=11, XML_ERROR_RECURSIVE_ENTITY_REF=12, XML_ERROR_ASYNC_ENTITY=13, XML_ERROR_BAD_CHAR_REF=14, XML_ERROR_BINARY_ENTITY_REF=15, XML_ERROR_ATTRIBUTE_EXTERNAL_ENTITY_REF=16, XML_ERROR_MISPLACED_XML_PI=17, XML_ERROR_UNKNOWN_ENCODING=18, XML_ERROR_INCORRECT_ENCODING=19, XML_ERROR_UNCLOSED_CDATA_SECTION=20, XML_ERROR_EXTERNAL_ENTITY_HANDLING=21, XML_ERROR_NOT_STANDALONE=22, XML_ERROR_UNEXPECTED_STATE=23, XML_ERROR_ENTITY_DECLARED_IN_PE=24, XML_ERROR_FEATURE_REQUIRES_XML_DTD=25, XML_ERROR_CANT_CHANGE_FEATURE_ONCE_PARSING=26, XML_ERROR_UNBOUND_PREFIX=27, XML_ERROR_UNDECLARING_PREFIX=28, XML_ERROR_INCOMPLETE_PE=29, XML_ERROR_XML_DECL=30, XML_ERROR_TEXT_DECL=31, XML_ERROR_PUBLICID=32, XML_ERROR_SUSPENDED=33, XML_ERROR_NOT_SUSPENDED=34, XML_ERROR_ABORTED=35, XML_ERROR_FINISHED=36, XML_ERROR_SUSPEND_PE=37, XML_ERROR_RESERVED_PREFIX_XML=38, XML_ERROR_RESERVED_PREFIX_XMLNS=39, XML_ERROR_RESERVED_NAMESPACE_URI=40, XML_ERROR_INVALID_ARGUMENT=41, XML_ERROR_NO_BUFFER=42, XML_ERROR_AMPLIFICATION_LIMIT_BREACH=43 };

// tag-XML_FeatureEnum
// file expat.h line 1000
enum XML_FeatureEnum { XML_FEATURE_END=0, XML_FEATURE_UNICODE=1, XML_FEATURE_UNICODE_WCHAR_T=2, XML_FEATURE_DTD=3, XML_FEATURE_CONTEXT_BYTES=4, XML_FEATURE_MIN_SIZE=5, XML_FEATURE_SIZEOF_XML_CHAR=6, XML_FEATURE_SIZEOF_XML_LCHAR=7, XML_FEATURE_NS=8, XML_FEATURE_LARGE_SIZE=9, XML_FEATURE_ATTR_INFO=10, XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_MAXIMUM_AMPLIFICATION_DEFAULT=11, XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_ACTIVATION_THRESHOLD_DEFAULT=12 };

// tag-XML_ParamEntityParsing
// file expat.h line 861
enum XML_ParamEntityParsing { XML_PARAM_ENTITY_PARSING_NEVER=0, XML_PARAM_ENTITY_PARSING_UNLESS_STANDALONE=1, XML_PARAM_ENTITY_PARSING_ALWAYS=2 };

// tag-XML_ParserStruct
// file expat.h line 50
struct XML_ParserStruct;

// tag-XML_Parsing
// file expat.h line 826
enum XML_Parsing { XML_INITIALIZED=0, XML_PARSING=1, XML_FINISHED=2, XML_SUSPENDED=3 };

// tag-XML_Status
// file expat.h line 70
enum XML_Status { XML_STATUS_ERROR=0, XML_STATUS_OK=1, XML_STATUS_SUSPENDED=2 };

// tag-XML_cp
// file expat.h line 166
struct XML_cp;

// tag-_IO_codecvt
// file /usr/include/bits/types/struct_FILE.h line 37
struct _IO_codecvt;

// tag-_IO_wide_data
// file /usr/include/bits/types/struct_FILE.h line 38
struct _IO_wide_data;

// tag-accounting
// file xmlparse.c line 411
struct accounting;

// tag-attribute_id
// file xmlparse.c line 250
struct attribute_id;

// tag-binding
// file xmlparse.c line 246
struct binding;

// tag-block
// file xmlparse.c line 319
struct block;

// tag-encoding
// file xmltok.h line 159
struct encoding;

// tag-entity_stats
// file xmlparse.c line 419
struct entity_stats;

// tag-open_internal_entity
// file xmlparse.c line 393
struct open_internal_entity;

// tag-position
// file xmltok.h line 146
struct position;

// tag-prefix
// file xmlparse.c line 247
struct prefix;

// tag-prolog_state
// file xmlrole.h line 118
struct prolog_state;

// tag-siphash
// file siphash.h line 132
struct siphash;

// tag-sipkey
// file siphash.h line 141
struct sipkey;

// tag-tag
// file xmlparse.c line 283
struct tag;


typedef struct anonymous$1 ATTRIBUTE;
typedef struct attribute_id ATTRIBUTE_ID;
typedef struct binding BINDING;
typedef struct block BLOCK;
typedef struct anonymous CONTENT_SCAFFOLD;
typedef signed int (*CONVERTER)(void *, const char *);
typedef struct anonymous$12 DEFAULT_ATTRIBUTE;
typedef struct anonymous$9 DTD;
typedef struct anonymous$10 ELEMENT_TYPE;
typedef struct encoding ENCODING;
typedef struct anonymous$3 ENTITY;
typedef struct _IO_FILE FILE;
typedef struct anonymous$5 HASH_TABLE;
typedef struct anonymous$6 HASH_TABLE_ITER;
typedef char ICHAR;
typedef struct anonymous$8 INIT_ENCODING;
typedef struct anonymous$7 NAMED;
typedef struct anonymous$11 NS_ATT;
typedef struct open_internal_entity OPEN_INTERNAL_ENTITY;
typedef struct position POSITION;
typedef struct prefix PREFIX;
typedef struct prolog_state PROLOG_STATE;
typedef signed int (*SCANNER)(const ENCODING *, const char *, const char *, const char **);
typedef struct anonymous$0 STRING_POOL;
typedef struct tag TAG;
typedef struct anonymous$13 TAG_NAME;
typedef unsigned char XML_Bool;
typedef const char XML_Char;
typedef const XML_Char *KEY;
typedef void (*XML_AttlistDeclHandler)(void *, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *, signed int);
typedef void (*XML_CharacterDataHandler)(void *, const XML_Char *, signed int);
typedef void (*XML_CommentHandler)(void *, const XML_Char *);
typedef struct XML_cp XML_Content;
typedef void (*XML_DefaultHandler)(void *, const XML_Char *, signed int);
typedef void (*XML_ElementDeclHandler)(void *, const XML_Char *, XML_Content *);
typedef struct anonymous$16 XML_Encoding;
typedef void (*XML_EndCdataSectionHandler)(void *);
typedef void (*XML_EndDoctypeDeclHandler)(void *);
typedef void (*XML_EndElementHandler)(void *, const XML_Char *);
typedef void (*XML_EndNamespaceDeclHandler)(void *, const XML_Char *);
typedef void (*XML_EntityDeclHandler)(void *, const XML_Char *, signed int, const XML_Char *, signed int, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *);
typedef struct anonymous$2 XML_Expat_Version;
typedef struct anonymous$14 XML_Feature;
typedef signed long int XML_Index;
typedef char XML_LChar;
typedef struct anonymous$4 XML_Memory_Handling_Suite;
typedef signed int (*XML_NotStandaloneHandler)(void *);
typedef void (*XML_NotationDeclHandler)(void *, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *);
typedef struct XML_ParserStruct *XML_Parser;
typedef static enum XML_Error Processor(XML_Parser, const char *, const char *, const char **);
typedef signed int (*XML_ExternalEntityRefHandler)(XML_Parser, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *);
typedef struct anonymous$15 XML_ParsingStatus;
typedef void (*XML_ProcessingInstructionHandler)(void *, const XML_Char *, const XML_Char *);
typedef unsigned long int XML_Size;
typedef void (*XML_SkippedEntityHandler)(void *, const XML_Char *, signed int);
typedef void (*XML_StartCdataSectionHandler)(void *);
typedef void (*XML_StartDoctypeDeclHandler)(void *, const XML_Char *, const XML_Char *, const XML_Char *, signed int);
typedef void (*XML_StartElementHandler)(void *, const XML_Char *, const XML_Char **);
typedef void (*XML_StartNamespaceDeclHandler)(void *, const XML_Char *, const XML_Char *);
typedef signed int (*XML_UnknownEncodingHandler)(void *, const XML_Char *, XML_Encoding *);
typedef void (*XML_UnparsedEntityDeclHandler)(void *, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *, const XML_Char *);
typedef void (*XML_XmlDeclHandler)(void *, const XML_Char *, const XML_Char *, signed int);
typedef unsigned long long int XmlBigCount;
typedef void _IO_lock_t;
typedef signed long int __off64_t;
typedef signed long int __off_t;
typedef signed long int ptrdiff_t;
typedef unsigned long int size_t;
typedef unsigned long int uint64_t;

// ENTROPY_DEBUG
// file xmlparse.c line 890
static unsigned long int ENTROPY_DEBUG(const char *label, unsigned long int entropy);
// XML_DefaultCurrent
// file xmlparse.c line 2333
void XML_DefaultCurrent(XML_Parser parser);
// XML_ErrorString
// file xmlparse.c line 2348
const XML_LChar * XML_ErrorString(enum XML_Error code);
// XML_ExpatVersion
// file xmlparse.c line 2453
const XML_LChar * XML_ExpatVersion(void);
// XML_ExpatVersionInfo
// file xmlparse.c line 2472
XML_Expat_Version XML_ExpatVersionInfo(void);
// XML_ExternalEntityParserCreate
// file xmlparse.c line 1248
XML_Parser XML_ExternalEntityParserCreate(XML_Parser oldParser, const XML_Char *context, const XML_Char *encodingName);
// XML_FreeContentModel
// file xmlparse.c line 2307
void XML_FreeContentModel(XML_Parser parser, XML_Content *model);
// XML_GetBase
// file xmlparse.c line 1552
const XML_Char * XML_GetBase(XML_Parser parser);
// XML_GetBuffer
// file xmlparse.c line 2036
void * XML_GetBuffer(XML_Parser parser, signed int len);
// XML_GetCurrentByteCount
// file xmlparse.c line 2254
signed int XML_GetCurrentByteCount(XML_Parser parser);
// XML_GetCurrentByteIndex
// file xmlparse.c line 2244
XML_Index XML_GetCurrentByteIndex(XML_Parser parser);
// XML_GetCurrentColumnNumber
// file xmlparse.c line 2295
XML_Size XML_GetCurrentColumnNumber(XML_Parser parser);
// XML_GetCurrentLineNumber
// file xmlparse.c line 2283
XML_Size XML_GetCurrentLineNumber(XML_Parser parser);
// XML_GetErrorCode
// file xmlparse.c line 2237
enum XML_Error XML_GetErrorCode(XML_Parser parser);
// XML_GetFeatureList
// file xmlparse.c line 2483
const XML_Feature * XML_GetFeatureList(void);
// XML_GetIdAttributeIndex
// file xmlparse.c line 1566
signed int XML_GetIdAttributeIndex(XML_Parser parser);
// XML_GetInputContext
// file xmlparse.c line 2263
const char * XML_GetInputContext(XML_Parser parser, signed int *offset, signed int *size);
// XML_GetParsingStatus
// file xmlparse.c line 2229
void XML_GetParsingStatus(XML_Parser parser, XML_ParsingStatus *status);
// XML_GetSpecifiedAttributeCount
// file xmlparse.c line 1559
signed int XML_GetSpecifiedAttributeCount(XML_Parser parser);
// XML_MemFree
// file xmlparse.c line 2327
void XML_MemFree(XML_Parser parser, void *ptr);
// XML_MemMalloc
// file xmlparse.c line 2313
void * XML_MemMalloc(XML_Parser parser, size_t size);
// XML_MemRealloc
// file xmlparse.c line 2320
void * XML_MemRealloc(XML_Parser parser, void *ptr, size_t size);
// XML_Parse
// file xmlparse.c line 1817
enum XML_Status XML_Parse(XML_Parser parser, const char *s, signed int len, signed int isFinal);
// XML_ParseBuffer
// file xmlparse.c line 1971
enum XML_Status XML_ParseBuffer(XML_Parser parser, signed int len, signed int isFinal);
// XML_ParserCreate
// file xmlparse.c line 715
XML_Parser XML_ParserCreate(const XML_Char *encodingName);
// XML_ParserCreateNS
// file xmlparse.c line 720
XML_Parser XML_ParserCreateNS(const XML_Char *encodingName, XML_Char nsSep);
// XML_ParserCreate_MM
// file xmlparse.c line 963
XML_Parser XML_ParserCreate_MM(const XML_Char *encodingName, const XML_Memory_Handling_Suite *memsuite, const XML_Char *nameSep);
// XML_ParserFree
// file xmlparse.c line 1428
void XML_ParserFree(XML_Parser parser);
// XML_ParserReset
// file xmlparse.c line 1180
XML_Bool XML_ParserReset(XML_Parser parser, const XML_Char *encodingName);
// XML_ResumeParser
// file xmlparse.c line 2189
enum XML_Status XML_ResumeParser(XML_Parser parser);
// XML_SetAttlistDeclHandler
// file xmlparse.c line 1768
void XML_SetAttlistDeclHandler(XML_Parser parser, XML_AttlistDeclHandler attdecl);
// XML_SetBase
// file xmlparse.c line 1538
enum XML_Status XML_SetBase(XML_Parser parser, const XML_Char *p);
// XML_SetBillionLaughsAttackProtectionActivationThreshold
// file xmlparse.c line 2543
XML_Bool XML_SetBillionLaughsAttackProtectionActivationThreshold(XML_Parser parser, unsigned long long int activationThresholdBytes);
// XML_SetBillionLaughsAttackProtectionMaximumAmplification
// file xmlparse.c line 2531
XML_Bool XML_SetBillionLaughsAttackProtectionMaximumAmplification(XML_Parser parser, float maximumAmplificationFactor);
// XML_SetCdataSectionHandler
// file xmlparse.c line 1623
void XML_SetCdataSectionHandler(XML_Parser parser, XML_StartCdataSectionHandler start, XML_EndCdataSectionHandler end);
// XML_SetCharacterDataHandler
// file xmlparse.c line 1603
void XML_SetCharacterDataHandler(XML_Parser parser, XML_CharacterDataHandler handler);
// XML_SetCommentHandler
// file xmlparse.c line 1617
void XML_SetCommentHandler(XML_Parser parser, XML_CommentHandler handler);
// XML_SetDefaultHandler
// file xmlparse.c line 1647
void XML_SetDefaultHandler(XML_Parser parser, XML_DefaultHandler handler);
// XML_SetDefaultHandlerExpand
// file xmlparse.c line 1655
void XML_SetDefaultHandlerExpand(XML_Parser parser, XML_DefaultHandler handler);
// XML_SetDoctypeDeclHandler
// file xmlparse.c line 1663
void XML_SetDoctypeDeclHandler(XML_Parser parser, XML_StartDoctypeDeclHandler start, XML_EndDoctypeDeclHandler end);
// XML_SetElementDeclHandler
// file xmlparse.c line 1762
void XML_SetElementDeclHandler(XML_Parser parser, XML_ElementDeclHandler eldecl);
// XML_SetElementHandler
// file xmlparse.c line 1582
void XML_SetElementHandler(XML_Parser parser, XML_StartElementHandler start, XML_EndElementHandler end);
// XML_SetEncoding
// file xmlparse.c line 1221
enum XML_Status XML_SetEncoding(XML_Parser parser, const XML_Char *encodingName);
// XML_SetEndCdataSectionHandler
// file xmlparse.c line 1640
void XML_SetEndCdataSectionHandler(XML_Parser parser, XML_EndCdataSectionHandler end);
// XML_SetEndDoctypeDeclHandler
// file xmlparse.c line 1679
void XML_SetEndDoctypeDeclHandler(XML_Parser parser, XML_EndDoctypeDeclHandler end);
// XML_SetEndElementHandler
// file xmlparse.c line 1597
void XML_SetEndElementHandler(XML_Parser parser, XML_EndElementHandler end);
// XML_SetEndNamespaceDeclHandler
// file xmlparse.c line 1715
void XML_SetEndNamespaceDeclHandler(XML_Parser parser, XML_EndNamespaceDeclHandler end);
// XML_SetEntityDeclHandler
// file xmlparse.c line 1774
void XML_SetEntityDeclHandler(XML_Parser parser, XML_EntityDeclHandler handler);
// XML_SetExternalEntityRefHandler
// file xmlparse.c line 1729
void XML_SetExternalEntityRefHandler(XML_Parser parser, XML_ExternalEntityRefHandler handler);
// XML_SetExternalEntityRefHandlerArg
// file xmlparse.c line 1736
void XML_SetExternalEntityRefHandlerArg(XML_Parser parser, void *arg);
// XML_SetHashSalt
// file xmlparse.c line 1803
signed int XML_SetHashSalt(XML_Parser parser, unsigned long int hash_salt);
// XML_SetNamespaceDeclHandler
// file xmlparse.c line 1698
void XML_SetNamespaceDeclHandler(XML_Parser parser, XML_StartNamespaceDeclHandler start, XML_EndNamespaceDeclHandler end);
// XML_SetNotStandaloneHandler
// file xmlparse.c line 1722
void XML_SetNotStandaloneHandler(XML_Parser parser, XML_NotStandaloneHandler handler);
// XML_SetNotationDeclHandler
// file xmlparse.c line 1692
void XML_SetNotationDeclHandler(XML_Parser parser, XML_NotationDeclHandler handler);
// XML_SetParamEntityParsing
// file xmlparse.c line 1786
signed int XML_SetParamEntityParsing(XML_Parser parser, enum XML_ParamEntityParsing peParsing);
// XML_SetProcessingInstructionHandler
// file xmlparse.c line 1610
void XML_SetProcessingInstructionHandler(XML_Parser parser, XML_ProcessingInstructionHandler handler);
// XML_SetReturnNSTriplet
// file xmlparse.c line 1517
void XML_SetReturnNSTriplet(XML_Parser parser, signed int do_nst);
// XML_SetSkippedEntityHandler
// file xmlparse.c line 1746
void XML_SetSkippedEntityHandler(XML_Parser parser, XML_SkippedEntityHandler handler);
// XML_SetStartCdataSectionHandler
// file xmlparse.c line 1633
void XML_SetStartCdataSectionHandler(XML_Parser parser, XML_StartCdataSectionHandler start);
// XML_SetStartDoctypeDeclHandler
// file xmlparse.c line 1672
void XML_SetStartDoctypeDeclHandler(XML_Parser parser, XML_StartDoctypeDeclHandler start);
// XML_SetStartElementHandler
// file xmlparse.c line 1591
void XML_SetStartElementHandler(XML_Parser parser, XML_StartElementHandler start);
// XML_SetStartNamespaceDeclHandler
// file xmlparse.c line 1708
void XML_SetStartNamespaceDeclHandler(XML_Parser parser, XML_StartNamespaceDeclHandler start);
// XML_SetUnknownEncodingHandler
// file xmlparse.c line 1753
void XML_SetUnknownEncodingHandler(XML_Parser parser, XML_UnknownEncodingHandler handler, void *data);
// XML_SetUnparsedEntityDeclHandler
// file xmlparse.c line 1685
void XML_SetUnparsedEntityDeclHandler(XML_Parser parser, XML_UnparsedEntityDeclHandler handler);
// XML_SetUserData
// file xmlparse.c line 1528
void XML_SetUserData(XML_Parser parser, void *p);
// XML_SetXmlDeclHandler
// file xmlparse.c line 1780
void XML_SetXmlDeclHandler(XML_Parser parser, XML_XmlDeclHandler handler);
// XML_StopParser
// file xmlparse.c line 2159
enum XML_Status XML_StopParser(XML_Parser parser, XML_Bool resumable);
// XML_UseForeignDTD
// file xmlparse.c line 1500
enum XML_Error XML_UseForeignDTD(XML_Parser parser, XML_Bool useDTD);
// XML_UseParserAsHandlerArg
// file xmlparse.c line 1494
void XML_UseParserAsHandlerArg(XML_Parser parser);
// XmlGetUtf8InternalEncoding
// file xmltok.h line 293
const ENCODING * XmlGetUtf8InternalEncoding(void);
// XmlGetUtf8InternalEncodingNS
// file xmltok.h line 311
const ENCODING * XmlGetUtf8InternalEncodingNS(void);
// XmlInitEncoding
// file xmltok.h line 292
signed int XmlInitEncoding(INIT_ENCODING *, const ENCODING **, const char *);
// XmlInitEncodingNS
// file xmltok.h line 310
signed int XmlInitEncodingNS(INIT_ENCODING *, const ENCODING **, const char *);
// XmlInitUnknownEncoding
// file xmltok.h line 301
ENCODING * XmlInitUnknownEncoding(void *, signed int *, CONVERTER, void *);
// XmlInitUnknownEncodingNS
// file xmltok.h line 313
ENCODING * XmlInitUnknownEncodingNS(void *, signed int *, CONVERTER, void *);
// XmlParseXmlDecl
// file xmltok.h line 286
signed int XmlParseXmlDecl(signed int, const ENCODING *, const char *, const char *, const char **, const char **, const char **, const char **, const ENCODING **, signed int *);
// XmlParseXmlDeclNS
// file xmltok.h line 304
signed int XmlParseXmlDeclNS(signed int, const ENCODING *, const char *, const char *, const char **, const char **, const char **, const char **, const ENCODING **, signed int *);
// XmlPrologStateInit
// file xmlrole.h line 130
void XmlPrologStateInit(PROLOG_STATE *);
// XmlPrologStateInitExternalEntity
// file xmlrole.h line 132
void XmlPrologStateInitExternalEntity(PROLOG_STATE *);
// XmlSizeOfUnknownEncoding
// file xmltok.h line 297
signed int XmlSizeOfUnknownEncoding(void);
// XmlUtf8Encode
// file xmltok.h line 295
signed int XmlUtf8Encode(signed int, char *);
// accountingDiffTolerated
// file xmlparse.c line 7568
static XML_Bool accountingDiffTolerated(XML_Parser originParser, signed int tok, const char *before, const char *after, signed int source_line, enum XML_Account account);
// accountingGetCurrentAmplification
// file xmlparse.c line 7493
static float accountingGetCurrentAmplification(XML_Parser rootParser);
// accountingOnAbort
// file xmlparse.c line 7526
static void accountingOnAbort(XML_Parser originParser);
// accountingReportDiff
// file xmlparse.c line 7531
static void accountingReportDiff(XML_Parser rootParser, unsigned int levelsAwayFromRootParser, const char *before, const char *after, ptrdiff_t bytesMore, signed int source_line, enum XML_Account account);
// accountingReportStats
// file xmlparse.c line 7507
static void accountingReportStats(XML_Parser originParser, const char *epilog);
// addBinding
// file xmlparse.c line 3711
static enum XML_Error addBinding(XML_Parser parser, PREFIX *prefix, const ATTRIBUTE_ID *attId, const XML_Char *uri, BINDING **bindingsPtr);
// appendAttributeValue
// file xmlparse.c line 5734
static enum XML_Error appendAttributeValue(XML_Parser parser, const ENCODING *enc, XML_Bool isCdata, const char *ptr, const char *end, STRING_POOL *pool, enum XML_Account account);
// arc4random_buf
// file xmlparse.c line 905 function generate_hash_secret_salt
signed int arc4random_buf(void);
// build_model
// file xmlparse.c line 7335
static XML_Content * build_model(XML_Parser parser);
// cdataSectionProcessor
// file xmlparse.c line 3864
static enum XML_Error cdataSectionProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// contentProcessor
// file xmlparse.c line 2608
static enum XML_Error contentProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// copyEntityTable
// file xmlparse.c line 6793
static signed int copyEntityTable(XML_Parser oldParser, HASH_TABLE *newTable, STRING_POOL *newPool, const HASH_TABLE *oldTable);
// copyString
// file xmlparse.c line 7470
static XML_Char * copyString(const XML_Char *s, const XML_Memory_Handling_Suite *memsuite);
// copy_salt_to_sipkey
// file xmlparse.c line 6874
static void copy_salt_to_sipkey(XML_Parser parser, struct sipkey *key);
// defineAttribute
// file xmlparse.c line 6234
static signed int defineAttribute(ELEMENT_TYPE *type, ATTRIBUTE_ID *attId, XML_Bool isCdata, XML_Bool isId, const XML_Char *value, XML_Parser parser);
// destroyBindings
// file xmlparse.c line 1416
static void destroyBindings(BINDING *bindings, XML_Parser parser);
// doCdataSection
// file xmlparse.c line 3887
static enum XML_Error doCdataSection(XML_Parser parser, const ENCODING *enc, const char **startPtr, const char *end, const char **nextPtr, XML_Bool haveMore, enum XML_Account account);
// doContent
// file xmlparse.c line 2737
static enum XML_Error doContent(XML_Parser parser, signed int startTagLevel, const ENCODING *enc, const char *s, const char *end, const char **nextPtr, XML_Bool haveMore, enum XML_Account account);
// doIgnoreSection
// file xmlparse.c line 4029
static enum XML_Error doIgnoreSection(XML_Parser parser, const ENCODING *enc, const char **startPtr, const char *end, const char **nextPtr, XML_Bool haveMore);
// doProlog
// file xmlparse.c line 4477
static enum XML_Error doProlog(XML_Parser parser, const ENCODING *enc, const char *s, const char *end, signed int tok, const char *next, const char **nextPtr, XML_Bool haveMore, XML_Bool allowClosingDoctype, enum XML_Account account);
// dtdCopy
// file xmlparse.c line 6667
static signed int dtdCopy(XML_Parser oldParser, DTD *newDtd, const DTD *oldDtd, const XML_Memory_Handling_Suite *ms);
// dtdCreate
// file xmlparse.c line 6564
static DTD * dtdCreate(const XML_Memory_Handling_Suite *ms);
// dtdDestroy
// file xmlparse.c line 6637
static void dtdDestroy(DTD *p, XML_Bool isDocEntity, const XML_Memory_Handling_Suite *ms);
// dtdReset
// file xmlparse.c line 6596
static void dtdReset(DTD *p, const XML_Memory_Handling_Suite *ms);
// entityTrackingOnClose
// file xmlparse.c line 7676
static void entityTrackingOnClose(XML_Parser originParser, ENTITY *entity, signed int sourceLine);
// entityTrackingOnOpen
// file xmlparse.c line 7661
static void entityTrackingOnOpen(XML_Parser originParser, ENTITY *entity, signed int sourceLine);
// entityTrackingReportStats
// file xmlparse.c line 7637
static void entityTrackingReportStats(XML_Parser rootParser, ENTITY *entity, const char *action, signed int sourceLine);
// entityValueInitProcessor
// file xmlparse.c line 4299
static enum XML_Error entityValueInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// entityValueProcessor
// file xmlparse.c line 4429
static enum XML_Error entityValueProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// epilogProcessor
// file xmlparse.c line 5508
static enum XML_Error epilogProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// errorProcessor
// file xmlparse.c line 5710
static enum XML_Error errorProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// externalEntityContentProcessor
// file xmlparse.c line 2723
static enum XML_Error externalEntityContentProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// externalEntityInitProcessor
// file xmlparse.c line 2621
static enum XML_Error externalEntityInitProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// externalEntityInitProcessor2
// file xmlparse.c line 2631
static enum XML_Error externalEntityInitProcessor2(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// externalEntityInitProcessor3
// file xmlparse.c line 2676
static enum XML_Error externalEntityInitProcessor3(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// externalParEntInitProcessor
// file xmlparse.c line 4279
static enum XML_Error externalParEntInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// externalParEntProcessor
// file xmlparse.c line 4383
static enum XML_Error externalParEntProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// freeBindings
// file xmlparse.c line 3211
static void freeBindings(XML_Parser parser, BINDING *bindings);
// generate_hash_secret_salt
// file xmlparse.c line 899
static unsigned long int generate_hash_secret_salt(XML_Parser parser);
// getAttributeId
// file xmlparse.c line 6324
static ATTRIBUTE_ID * getAttributeId(XML_Parser parser, const ENCODING *enc, const char *start, const char *end);
// getContext
// file xmlparse.c line 6387
static const XML_Char * getContext(XML_Parser parser);
// getDebugLevel
// file xmlparse.c line 8224
static unsigned long int getDebugLevel(const char *variableName, unsigned long int defaultDebugLevel);
// getElementType
// file xmlparse.c line 7447
static ELEMENT_TYPE * getElementType(XML_Parser parser, const ENCODING *enc, const char *ptr, const char *end);
// getRootParserOf
// file xmlparse.c line 7685
static XML_Parser getRootParserOf(XML_Parser parser, unsigned int *outLevelDiff);
// get_hash_secret_salt
// file xmlparse.c line 942
static unsigned long int get_hash_secret_salt(XML_Parser parser);
// handleUnknownEncoding
// file xmlparse.c line 4233
static enum XML_Error handleUnknownEncoding(XML_Parser parser, const XML_Char *encodingName);
// hash
// file xmlparse.c line 6880
static unsigned long int hash(XML_Parser parser, KEY s);
// hashTableClear
// file xmlparse.c line 6980
static void hashTableClear(HASH_TABLE *table);
// hashTableDestroy
// file xmlparse.c line 6990
static void hashTableDestroy(HASH_TABLE *table);
// hashTableInit
// file xmlparse.c line 6998
static void hashTableInit(HASH_TABLE *p, const XML_Memory_Handling_Suite *ms);
// hashTableIterInit
// file xmlparse.c line 7007
static void hashTableIterInit(HASH_TABLE_ITER *iter, const HASH_TABLE *table);
// hashTableIterNext
// file xmlparse.c line 7013
static NAMED * hashTableIterNext(HASH_TABLE_ITER *iter);
// ignoreSectionProcessor
// file xmlparse.c line 4011
static enum XML_Error ignoreSectionProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr);
// initializeEncoding
// file xmlparse.c line 4111
static enum XML_Error initializeEncoding(XML_Parser parser);
// internalEntityProcessor
// file xmlparse.c line 5643
static enum XML_Error internalEntityProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// keyeq
// file xmlparse.c line 6858
static XML_Bool keyeq(KEY s1, KEY s2);
// keylen
// file xmlparse.c line 6866
static size_t keylen(KEY s);
// lookup
// file xmlparse.c line 6891
static NAMED * lookup(XML_Parser parser, HASH_TABLE *table, KEY name, size_t createSize);
// memcmp
// file /usr/include/string.h line 64
extern signed int memcmp(const void *, const void *, size_t);
// memcpy
// file /usr/include/string.h line 43
extern void * memcpy(void *, const void *, size_t);
// memmove
// file /usr/include/string.h line 47
extern void * memmove(void *, const void *, size_t);
// moveToFreeBindingList
// file xmlparse.c line 1170
static void moveToFreeBindingList(XML_Parser parser, BINDING *bindings);
// nextScaffoldPart
// file xmlparse.c line 7274
static signed int nextScaffoldPart(XML_Parser parser);
// normalizeLines
// file xmlparse.c line 6120
static void normalizeLines(XML_Char *s);
// normalizePublicId
// file xmlparse.c line 6543
static void normalizePublicId(XML_Char *publicId);
// parserCreate
// file xmlparse.c line 970
static XML_Parser parserCreate(const XML_Char *encodingName, const XML_Memory_Handling_Suite *memsuite, const XML_Char *nameSep, DTD *dtd);
// parserInit
// file xmlparse.c line 1085
static void parserInit(XML_Parser parser, const XML_Char *encodingName);
// poolAppend
// file xmlparse.c line 7068
static XML_Char * poolAppend(STRING_POOL *pool, const ENCODING *enc, const char *ptr, const char *end);
// poolAppendString
// file xmlparse.c line 7121
static const XML_Char * poolAppendString(STRING_POOL *pool, const XML_Char *s);
// poolBytesToAllocateFor
// file xmlparse.c line 7142
static size_t poolBytesToAllocateFor(signed int blockSize);
// poolClear
// file xmlparse.c line 7033
static void poolClear(STRING_POOL *pool);
// poolCopyString
// file xmlparse.c line 7085
static const XML_Char * poolCopyString(STRING_POOL *pool, const XML_Char *s);
// poolCopyStringN
// file xmlparse.c line 7096
static const XML_Char * poolCopyStringN(STRING_POOL *pool, const XML_Char *s, signed int n);
// poolDestroy
// file xmlparse.c line 7052
static void poolDestroy(STRING_POOL *pool);
// poolGrow
// file xmlparse.c line 7170
static XML_Bool poolGrow(STRING_POOL *pool);
// poolInit
// file xmlparse.c line 7023
static void poolInit(STRING_POOL *pool, const XML_Memory_Handling_Suite *ms);
// poolStoreString
// file xmlparse.c line 7131
static XML_Char * poolStoreString(STRING_POOL *pool, const ENCODING *enc, const char *ptr, const char *end);
// processInternalEntity
// file xmlparse.c line 5579
static enum XML_Error processInternalEntity(XML_Parser parser, ENTITY *entity, XML_Bool betweenDecl);
// processXmlDecl
// file xmlparse.c line 4141
static enum XML_Error processXmlDecl(XML_Parser parser, signed int isGeneralTextEntity, const char *s, const char *next);
// prologInitProcessor
// file xmlparse.c line 4267
static enum XML_Error prologInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// prologProcessor
// file xmlparse.c line 4467
static enum XML_Error prologProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr);
// reportComment
// file xmlparse.c line 6168
static signed int reportComment(XML_Parser parser, const ENCODING *enc, const char *start, const char *end);
// reportDefault
// file xmlparse.c line 6188
static void reportDefault(XML_Parser parser, const ENCODING *enc, const char *s, const char *end);
// reportProcessingInstruction
// file xmlparse.c line 6141
static signed int reportProcessingInstruction(XML_Parser parser, const ENCODING *enc, const char *start, const char *end);
// setContext
// file xmlparse.c line 6483
static XML_Bool setContext(XML_Parser parser, const XML_Char *context);
// setElementTypePrefix
// file xmlparse.c line 6295
static signed int setElementTypePrefix(XML_Parser parser, ELEMENT_TYPE *elementType);
// sip24_final
// file siphash.h line 231
static uint64_t sip24_final(struct siphash *H);
// sip24_init
// file siphash.h line 192
static struct siphash * sip24_init(struct siphash *H, const struct sipkey *key);
// sip24_update
// file siphash.h line 207
static struct siphash * sip24_update(struct siphash *H, const void *src, size_t len);
// sip24_valid
// file siphash.h line 288
static signed int sip24_valid(void);
// sip_round
// file siphash.h line 167
static void sip_round(struct siphash *H, const signed int rounds);
// sip_tokey
// file siphash.h line 148
static struct sipkey * sip_tokey(struct sipkey *key, const void *src);
// siphash24
// file siphash.h line 271
static uint64_t siphash24(const void *src, size_t len, const struct sipkey *key);
// startParsing
// file xmlparse.c line 949
static XML_Bool startParsing(XML_Parser parser);
// storeAttributeValue
// file xmlparse.c line 5719
static enum XML_Error storeAttributeValue(XML_Parser parser, const ENCODING *enc, XML_Bool isCdata, const char *ptr, const char *end, STRING_POOL *pool, enum XML_Account account);
// storeAtts
// file xmlparse.c line 3239
static enum XML_Error storeAtts(XML_Parser parser, const ENCODING *enc, const char *attStr, TAG_NAME *tagNamePtr, BINDING **bindingsPtr, enum XML_Account account);
// storeEntityValue
// file xmlparse.c line 5934
static enum XML_Error storeEntityValue(XML_Parser parser, const ENCODING *enc, const char *entityTextPtr, const char *entityTextEnd, enum XML_Account account);
// storeRawNames
// file xmlparse.c line 2559
static XML_Bool storeRawNames(XML_Parser parser);
// testingAccountingGetCountBytesDirect
// file xmlparse.c line 7623
unsigned long long int testingAccountingGetCountBytesDirect(XML_Parser parser);
// testingAccountingGetCountBytesIndirect
// file xmlparse.c line 7630
unsigned long long int testingAccountingGetCountBytesIndirect(XML_Parser parser);
// unsignedCharToPrintable
// file xmlparse.c line 7700
const char * unsignedCharToPrintable(unsigned char c);

struct anonymous$6
{
  // p
  NAMED **p;
  // end
  NAMED **end;
};

struct anonymous$5
{
  // v
  NAMED **v;
  // power
  unsigned char power;
  // size
  size_t size;
  // used
  size_t used;
  // mem
  const XML_Memory_Handling_Suite *mem;
};

struct anonymous$4
{
  // malloc_fcn
  void * (*malloc_fcn)(size_t);
  // realloc_fcn
  void * (*realloc_fcn)(void *, size_t);
  // free_fcn
  void (*free_fcn)(void *);
};

struct anonymous$0
{
  // blocks
  BLOCK *blocks;
  // freeBlocks
  BLOCK *freeBlocks;
  // end
  const XML_Char *end;
  // ptr
  XML_Char *ptr;
  // start
  XML_Char *start;
  // mem
  const XML_Memory_Handling_Suite *mem;
};

struct anonymous$7
{
  // name
  KEY name;
};

struct anonymous$10
{
  // name
  const XML_Char *name;
  // prefix
  PREFIX *prefix;
  // idAtt
  const ATTRIBUTE_ID *idAtt;
  // nDefaultAtts
  signed int nDefaultAtts;
  // allocDefaultAtts
  signed int allocDefaultAtts;
  // defaultAtts
  DEFAULT_ATTRIBUTE *defaultAtts;
};

struct anonymous$3
{
  // name
  const XML_Char *name;
  // textPtr
  const XML_Char *textPtr;
  // textLen
  signed int textLen;
  // processed
  signed int processed;
  // systemId
  const XML_Char *systemId;
  // base
  const XML_Char *base;
  // publicId
  const XML_Char *publicId;
  // notation
  const XML_Char *notation;
  // open
  XML_Bool open;
  // is_param
  XML_Bool is_param;
  // is_internal
  XML_Bool is_internal;
};

struct anonymous$1
{
  // name
  const char *name;
  // valuePtr
  const char *valuePtr;
  // valueEnd
  const char *valueEnd;
  // normalized
  char normalized;
};

struct anonymous$13
{
  // str
  const XML_Char *str;
  // localPart
  const XML_Char *localPart;
  // prefix
  const XML_Char *prefix;
  // strLen
  signed int strLen;
  // uriLen
  signed int uriLen;
  // prefixLen
  signed int prefixLen;
};

struct anonymous$12
{
  // id
  const ATTRIBUTE_ID *id;
  // isCdata
  XML_Bool isCdata;
  // value
  const XML_Char *value;
};

struct anonymous$16
{
  // map
  signed int map[256l];
  // data
  void *data;
  // convert
  signed int (*convert)(void *, const char *);
  // release
  void (*release)(void *);
};

struct anonymous$14
{
  // feature
  enum XML_FeatureEnum feature;
  // name
  const XML_LChar *name;
  // value
  signed long int value;
};

struct anonymous$15
{
  // parsing
  enum XML_Parsing parsing;
  // finalBuffer
  XML_Bool finalBuffer;
};

struct anonymous
{
  // type
  enum XML_Content_Type type;
  // quant
  enum XML_Content_Quant quant;
  // name
  const XML_Char *name;
  // firstchild
  signed int firstchild;
  // lastchild
  signed int lastchild;
  // childcnt
  signed int childcnt;
  // nextsib
  signed int nextsib;
};

struct anonymous$2
{
  // major
  signed int major;
  // minor
  signed int minor;
  // micro
  signed int micro;
};

typedef struct prefix
{
  // name
  const XML_Char *name;
  // binding
  BINDING *binding;
} PREFIX;

struct anonymous$9
{
  // generalEntities
  HASH_TABLE generalEntities;
  // elementTypes
  HASH_TABLE elementTypes;
  // attributeIds
  HASH_TABLE attributeIds;
  // prefixes
  HASH_TABLE prefixes;
  // pool
  STRING_POOL pool;
  // entityValuePool
  STRING_POOL entityValuePool;
  // keepProcessing
  XML_Bool keepProcessing;
  // hasParamEntityRefs
  XML_Bool hasParamEntityRefs;
  // standalone
  XML_Bool standalone;
  // paramEntityRead
  XML_Bool paramEntityRead;
  // paramEntities
  HASH_TABLE paramEntities;
  // defaultPrefix
  PREFIX defaultPrefix;
  // in_eldecl
  XML_Bool in_eldecl;
  // scaffold
  CONTENT_SCAFFOLD *scaffold;
  // contentStringLen
  unsigned int contentStringLen;
  // scaffSize
  unsigned int scaffSize;
  // scaffCount
  unsigned int scaffCount;
  // scaffLevel
  signed int scaffLevel;
  // scaffIndex
  signed int *scaffIndex;
};

typedef struct encoding
{
  // scanners
  SCANNER scanners[4l];
  // literalScanners
  SCANNER literalScanners[2l];
  // nameMatchesAscii
  signed int (*nameMatchesAscii)(const ENCODING *, const char *, const char *, const char *);
  // nameLength
  signed int (*nameLength)(const ENCODING *, const char *);
  // skipS
  const char * (*skipS)(const ENCODING *, const char *);
  // getAtts
  signed int (*getAtts)(const ENCODING *, const char *, signed int, ATTRIBUTE *);
  // charRefNumber
  signed int (*charRefNumber)(const ENCODING *, const char *);
  // predefinedEntityName
  signed int (*predefinedEntityName)(const ENCODING *, const char *, const char *);
  // updatePosition
  void (*updatePosition)(const ENCODING *, const char *, const char *, POSITION *);
  // isPublicId
  signed int (*isPublicId)(const ENCODING *, const char *, const char *, const char **);
  // utf8Convert
  enum XML_Convert_Result (*utf8Convert)(const ENCODING *, const char **, const char *, char **, const char *);
  // utf16Convert
  enum XML_Convert_Result (*utf16Convert)(const ENCODING *, const char **, const char *, unsigned short int **, const unsigned short int *);
  // minBytesPerChar
  signed int minBytesPerChar;
  // isUtf8
  char isUtf8;
  // isUtf16
  char isUtf16;
} ENCODING;

struct anonymous$8
{
  // initEnc
  ENCODING initEnc;
  // encPtr
  const ENCODING **encPtr;
};

struct anonymous$11
{
  // version
  unsigned long int version;
  // hash
  unsigned long int hash;
  // uriName
  const XML_Char *uriName;
};

typedef struct prolog_state
{
  // handler
  signed int (*handler)(struct prolog_state *, signed int, const char *, const char *, const ENCODING *);
  // level
  unsigned int level;
  // role_none
  signed int role_none;
  // includeLevel
  unsigned int includeLevel;
  // documentEntity
  signed int documentEntity;
  // inEntityValue
  signed int inEntityValue;
} PROLOG_STATE;

typedef struct position
{
  // lineNumber
  XML_Size lineNumber;
  // columnNumber
  XML_Size columnNumber;
} POSITION;

typedef struct accounting
{
  // countBytesDirect
  XmlBigCount countBytesDirect;
  // countBytesIndirect
  XmlBigCount countBytesIndirect;
  // debugLevel
  signed int debugLevel;
  // maximumAmplificationFactor
  float maximumAmplificationFactor;
  // activationThresholdBytes
  unsigned long long int activationThresholdBytes;
} ACCOUNTING;

typedef struct entity_stats
{
  // countEverOpened
  unsigned int countEverOpened;
  // currentDepth
  unsigned int currentDepth;
  // maximumDepthSeen
  unsigned int maximumDepthSeen;
  // debugLevel
  signed int debugLevel;
} ENTITY_STATS;

struct XML_ParserStruct
{
  // m_userData
  void *m_userData;
  // m_handlerArg
  void *m_handlerArg;
  // m_buffer
  char *m_buffer;
  // m_mem
  const XML_Memory_Handling_Suite m_mem;
  // m_bufferPtr
  const char *m_bufferPtr;
  // m_bufferEnd
  char *m_bufferEnd;
  // m_bufferLim
  const char *m_bufferLim;
  // m_parseEndByteIndex
  XML_Index m_parseEndByteIndex;
  // m_parseEndPtr
  const char *m_parseEndPtr;
  // m_dataBuf
  XML_Char *m_dataBuf;
  // m_dataBufEnd
  XML_Char *m_dataBufEnd;
  // m_startElementHandler
  XML_StartElementHandler m_startElementHandler;
  // m_endElementHandler
  XML_EndElementHandler m_endElementHandler;
  // m_characterDataHandler
  XML_CharacterDataHandler m_characterDataHandler;
  // m_processingInstructionHandler
  XML_ProcessingInstructionHandler m_processingInstructionHandler;
  // m_commentHandler
  XML_CommentHandler m_commentHandler;
  // m_startCdataSectionHandler
  XML_StartCdataSectionHandler m_startCdataSectionHandler;
  // m_endCdataSectionHandler
  XML_EndCdataSectionHandler m_endCdataSectionHandler;
  // m_defaultHandler
  XML_DefaultHandler m_defaultHandler;
  // m_startDoctypeDeclHandler
  XML_StartDoctypeDeclHandler m_startDoctypeDeclHandler;
  // m_endDoctypeDeclHandler
  XML_EndDoctypeDeclHandler m_endDoctypeDeclHandler;
  // m_unparsedEntityDeclHandler
  XML_UnparsedEntityDeclHandler m_unparsedEntityDeclHandler;
  // m_notationDeclHandler
  XML_NotationDeclHandler m_notationDeclHandler;
  // m_startNamespaceDeclHandler
  XML_StartNamespaceDeclHandler m_startNamespaceDeclHandler;
  // m_endNamespaceDeclHandler
  XML_EndNamespaceDeclHandler m_endNamespaceDeclHandler;
  // m_notStandaloneHandler
  XML_NotStandaloneHandler m_notStandaloneHandler;
  // m_externalEntityRefHandler
  XML_ExternalEntityRefHandler m_externalEntityRefHandler;
  // m_externalEntityRefHandlerArg
  XML_Parser m_externalEntityRefHandlerArg;
  // m_skippedEntityHandler
  XML_SkippedEntityHandler m_skippedEntityHandler;
  // m_unknownEncodingHandler
  XML_UnknownEncodingHandler m_unknownEncodingHandler;
  // m_elementDeclHandler
  XML_ElementDeclHandler m_elementDeclHandler;
  // m_attlistDeclHandler
  XML_AttlistDeclHandler m_attlistDeclHandler;
  // m_entityDeclHandler
  XML_EntityDeclHandler m_entityDeclHandler;
  // m_xmlDeclHandler
  XML_XmlDeclHandler m_xmlDeclHandler;
  // m_encoding
  const ENCODING *m_encoding;
  // m_initEncoding
  INIT_ENCODING m_initEncoding;
  // m_internalEncoding
  const ENCODING *m_internalEncoding;
  // m_protocolEncodingName
  const XML_Char *m_protocolEncodingName;
  // m_ns
  XML_Bool m_ns;
  // m_ns_triplets
  XML_Bool m_ns_triplets;
  // m_unknownEncodingMem
  void *m_unknownEncodingMem;
  // m_unknownEncodingData
  void *m_unknownEncodingData;
  // m_unknownEncodingHandlerData
  void *m_unknownEncodingHandlerData;
  // m_unknownEncodingRelease
  void (*m_unknownEncodingRelease)(void *);
  // m_prologState
  PROLOG_STATE m_prologState;
  // m_processor
  Processor (*m_processor);
  // m_errorCode
  enum XML_Error m_errorCode;
  // m_eventPtr
  const char *m_eventPtr;
  // m_eventEndPtr
  const char *m_eventEndPtr;
  // m_positionPtr
  const char *m_positionPtr;
  // m_openInternalEntities
  OPEN_INTERNAL_ENTITY *m_openInternalEntities;
  // m_freeInternalEntities
  OPEN_INTERNAL_ENTITY *m_freeInternalEntities;
  // m_defaultExpandInternalEntities
  XML_Bool m_defaultExpandInternalEntities;
  // m_tagLevel
  signed int m_tagLevel;
  // m_declEntity
  ENTITY *m_declEntity;
  // m_doctypeName
  const XML_Char *m_doctypeName;
  // m_doctypeSysid
  const XML_Char *m_doctypeSysid;
  // m_doctypePubid
  const XML_Char *m_doctypePubid;
  // m_declAttributeType
  const XML_Char *m_declAttributeType;
  // m_declNotationName
  const XML_Char *m_declNotationName;
  // m_declNotationPublicId
  const XML_Char *m_declNotationPublicId;
  // m_declElementType
  ELEMENT_TYPE *m_declElementType;
  // m_declAttributeId
  ATTRIBUTE_ID *m_declAttributeId;
  // m_declAttributeIsCdata
  XML_Bool m_declAttributeIsCdata;
  // m_declAttributeIsId
  XML_Bool m_declAttributeIsId;
  // m_dtd
  DTD *m_dtd;
  // m_curBase
  const XML_Char *m_curBase;
  // m_tagStack
  TAG *m_tagStack;
  // m_freeTagList
  TAG *m_freeTagList;
  // m_inheritedBindings
  BINDING *m_inheritedBindings;
  // m_freeBindingList
  BINDING *m_freeBindingList;
  // m_attsSize
  signed int m_attsSize;
  // m_nSpecifiedAtts
  signed int m_nSpecifiedAtts;
  // m_idAttIndex
  signed int m_idAttIndex;
  // m_atts
  ATTRIBUTE *m_atts;
  // m_nsAtts
  NS_ATT *m_nsAtts;
  // m_nsAttsVersion
  unsigned long int m_nsAttsVersion;
  // m_nsAttsPower
  unsigned char m_nsAttsPower;
  // m_position
  POSITION m_position;
  // m_tempPool
  STRING_POOL m_tempPool;
  // m_temp2Pool
  STRING_POOL m_temp2Pool;
  // m_groupConnector
  char *m_groupConnector;
  // m_groupSize
  unsigned int m_groupSize;
  // m_namespaceSeparator
  XML_Char m_namespaceSeparator;
  // m_parentParser
  XML_Parser m_parentParser;
  // m_parsingStatus
  XML_ParsingStatus m_parsingStatus;
  // m_isParamEntity
  XML_Bool m_isParamEntity;
  // m_useForeignDTD
  XML_Bool m_useForeignDTD;
  // m_paramEntityParsing
  enum XML_ParamEntityParsing m_paramEntityParsing;
  // m_hash_secret_salt
  unsigned long int m_hash_secret_salt;
  // m_accounting
  ACCOUNTING m_accounting;
  // m_entity_stats
  ENTITY_STATS m_entity_stats;
};

struct XML_cp
{
  // type
  enum XML_Content_Type type;
  // quant
  enum XML_Content_Quant quant;
  // name
  XML_Char *name;
  // numchildren
  unsigned int numchildren;
  // children
  XML_Content *children;
};

struct _IO_codecvt
{
};

struct _IO_wide_data
{
};

struct attribute_id
{
  // name
  XML_Char *name;
  // prefix
  PREFIX *prefix;
  // maybeTokenized
  XML_Bool maybeTokenized;
  // xmlns
  XML_Bool xmlns;
};

struct binding
{
  // prefix
  struct prefix *prefix;
  // nextTagBinding
  struct binding *nextTagBinding;
  // prevPrefixBinding
  struct binding *prevPrefixBinding;
  // attId
  const struct attribute_id *attId;
  // uri
  XML_Char *uri;
  // uriLen
  signed int uriLen;
  // uriAlloc
  signed int uriAlloc;
};

struct block
{
  // next
  struct block *next;
  // size
  signed int size;
  // s
  XML_Char s[1l];
};

struct open_internal_entity
{
  // internalEventPtr
  const char *internalEventPtr;
  // internalEventEndPtr
  const char *internalEventEndPtr;
  // next
  struct open_internal_entity *next;
  // entity
  ENTITY *entity;
  // startTagLevel
  signed int startTagLevel;
  // betweenDecl
  XML_Bool betweenDecl;
};

struct siphash
{
  // v0
  uint64_t v0;
  // v1
  uint64_t v1;
  // v2
  uint64_t v2;
  // v3
  uint64_t v3;
  // buf
  unsigned char buf[8l];
  // p
  unsigned char *p;
  // c
  uint64_t c;
};

struct sipkey
{
  // k
  uint64_t k[2l];
};

struct tag
{
  // parent
  struct tag *parent;
  // rawName
  const char *rawName;
  // rawNameLength
  signed int rawNameLength;
  // name
  TAG_NAME name;
  // buf
  char *buf;
  // bufEnd
  char *bufEnd;
  // bindings
  BINDING *bindings;
};


// implicitContext
// file xmlparse.c line 725
static const XML_Char implicitContext[41l]={ 'x', 'm', 'l', '=', 'h', 't', 't', 'p', ':', '/', '/', 'w', 'w', 'w', '.', 'w', '3', '.', 'o', 'r', 'g', '/', 'X', 'M', 'L', '/', '1', '9', '9', '8', '/', 'n', 'a', 'm', 'e', 's', 'p', 'a', 'c', 'e', 0 };
// stderr
// file /usr/include/stdio.h line 145
extern FILE *stderr;

// ENTROPY_DEBUG
// file xmlparse.c line 890
static unsigned long int ENTROPY_DEBUG(const char *label, unsigned long int entropy)
{
  unsigned long int return_value_getDebugLevel=getDebugLevel("EXPAT_ENTROPY_DEBUG", 0ul);
  if(return_value_getDebugLevel >= 1ul)
    fprintf(stderr, "expat: Entropy: %s --> 0x%0*lx (%lu bytes)\n", label, (signed int)sizeof(unsigned long int) /*8*/  * 2, entropy, sizeof(unsigned long int) /*8ul*/ );

  return entropy;
}

// XML_DefaultCurrent
// file xmlparse.c line 2333
void XML_DefaultCurrent(XML_Parser parser)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
    {
      if(!(parser->m_openInternalEntities == ((OPEN_INTERNAL_ENTITY *)NULL)))
        reportDefault(parser, parser->m_internalEncoding, parser->m_openInternalEntities->internalEventPtr, parser->m_openInternalEntities->internalEventEndPtr);

      else
        reportDefault(parser, parser->m_encoding, parser->m_eventPtr, parser->m_eventEndPtr);
    }

  }

}

// XML_ErrorString
// file xmlparse.c line 2348
const XML_LChar * XML_ErrorString(enum XML_Error code)
{
  switch((signed int)code)
  {
    case 0:
      return ((const XML_LChar *)NULL);
    case 1:
      return "out of memory";
    case 2:
      return "syntax error";
    case 3:
      return "no element found";
    case 4:
      return "not well-formed (invalid token)";
    case 5:
      return "unclosed token";
    case 6:
      return "partial character";
    case 7:
      return "mismatched tag";
    case 8:
      return "duplicate attribute";
    case 9:
      return "junk after document element";
    case 10:
      return "illegal parameter entity reference";
    case 11:
      return "undefined entity";
    case 12:
      return "recursive entity reference";
    case 13:
      return "asynchronous entity";
    case 14:
      return "reference to invalid character number";
    case 15:
      return "reference to binary entity";
    case 16:
      return "reference to external entity in attribute";
    case 17:
      return "XML or text declaration not at start of entity";
    case 18:
      return "unknown encoding";
    case 19:
      return "encoding specified in XML declaration is incorrect";
    case 20:
      return "unclosed CDATA section";
    case 21:
      return "error in processing external entity reference";
    case 22:
      return "document is not standalone";
    case 23:
      return "unexpected parser state - please send a bug report";
    case 24:
      return "entity declared in parameter entity";
    case 25:
      return "requested feature requires XML_DTD support in Expat";
    case 26:
      return "cannot change setting once parsing has begun";
    case 27:
      return "unbound prefix";
    case 28:
      return "must not undeclare prefix";
    case 29:
      return "incomplete markup in parameter entity";
    case 30:
      return "XML declaration not well-formed";
    case 31:
      return "text declaration not well-formed";
    case 32:
      return "illegal character(s) in public id";
    case 33:
      return "parser suspended";
    case 34:
      return "parser not suspended";
    case 35:
      return "parsing aborted";
    case 36:
      return "parsing finished";
    case 37:
      return "cannot suspend in external parameter entity";
    case 38:
      return "reserved prefix (xml) must not be undeclared or bound to another namespace name";
    case 39:
      return "reserved prefix (xmlns) must not be declared or undeclared";
    case 40:
      return "prefix must not be bound to one of the reserved namespace names";
    case 41:
      return "invalid argument";
    case 42:
      return "a successful prior call to function XML_GetBuffer is required";
    case 43:
      return "limit on input amplification factor (from DTD and entities) breached";
    default:
      return ((const XML_LChar *)NULL);
  }
}

// XML_ExpatVersion
// file xmlparse.c line 2453
const XML_LChar * XML_ExpatVersion(void)
{
  return "expat_2.4.4";
}

// XML_ExpatVersionInfo
// file xmlparse.c line 2472
XML_Expat_Version XML_ExpatVersionInfo(void)
{
  XML_Expat_Version version;
  version.major = 2;
  version.minor = 4;
  version.micro = 4;
  return version;
}

// XML_ExternalEntityParserCreate
// file xmlparse.c line 1248
XML_Parser XML_ExternalEntityParserCreate(XML_Parser oldParser, const XML_Char *context, const XML_Char *encodingName)
{
  XML_Parser parser=oldParser;
  DTD *newDtd=((DTD *)NULL);
  DTD *oldDtd;
  XML_StartElementHandler oldStartElementHandler;
  XML_EndElementHandler oldEndElementHandler;
  XML_CharacterDataHandler oldCharacterDataHandler;
  XML_ProcessingInstructionHandler oldProcessingInstructionHandler;
  XML_CommentHandler oldCommentHandler;
  XML_StartCdataSectionHandler oldStartCdataSectionHandler;
  XML_EndCdataSectionHandler oldEndCdataSectionHandler;
  XML_DefaultHandler oldDefaultHandler;
  XML_UnparsedEntityDeclHandler oldUnparsedEntityDeclHandler;
  XML_NotationDeclHandler oldNotationDeclHandler;
  XML_StartNamespaceDeclHandler oldStartNamespaceDeclHandler;
  XML_EndNamespaceDeclHandler oldEndNamespaceDeclHandler;
  XML_NotStandaloneHandler oldNotStandaloneHandler;
  XML_ExternalEntityRefHandler oldExternalEntityRefHandler;
  XML_SkippedEntityHandler oldSkippedEntityHandler;
  XML_UnknownEncodingHandler oldUnknownEncodingHandler;
  XML_ElementDeclHandler oldElementDeclHandler;
  XML_AttlistDeclHandler oldAttlistDeclHandler;
  XML_EntityDeclHandler oldEntityDeclHandler;
  XML_XmlDeclHandler oldXmlDeclHandler;
  ELEMENT_TYPE *oldDeclElementType;
  void *oldUserData;
  void *oldHandlerArg;
  XML_Bool oldDefaultExpandInternalEntities;
  XML_Parser oldExternalEntityRefHandlerArg;
  enum XML_ParamEntityParsing oldParamEntityParsing;
  signed int oldInEntityValue;
  XML_Bool oldns_triplets;
  unsigned long int oldhash_secret_salt;
  XML_Bool return_value_setContext;
  if(oldParser == ((XML_Parser)NULL))
    return ((XML_Parser)NULL);

  else
  {
    oldDtd = parser->m_dtd;
    oldStartElementHandler = parser->m_startElementHandler;
    oldEndElementHandler = parser->m_endElementHandler;
    oldCharacterDataHandler = parser->m_characterDataHandler;
    oldProcessingInstructionHandler = parser->m_processingInstructionHandler;
    oldCommentHandler = parser->m_commentHandler;
    oldStartCdataSectionHandler = parser->m_startCdataSectionHandler;
    oldEndCdataSectionHandler = parser->m_endCdataSectionHandler;
    oldDefaultHandler = parser->m_defaultHandler;
    oldUnparsedEntityDeclHandler = parser->m_unparsedEntityDeclHandler;
    oldNotationDeclHandler = parser->m_notationDeclHandler;
    oldStartNamespaceDeclHandler = parser->m_startNamespaceDeclHandler;
    oldEndNamespaceDeclHandler = parser->m_endNamespaceDeclHandler;
    oldNotStandaloneHandler = parser->m_notStandaloneHandler;
    oldExternalEntityRefHandler = parser->m_externalEntityRefHandler;
    oldSkippedEntityHandler = parser->m_skippedEntityHandler;
    oldUnknownEncodingHandler = parser->m_unknownEncodingHandler;
    oldElementDeclHandler = parser->m_elementDeclHandler;
    oldAttlistDeclHandler = parser->m_attlistDeclHandler;
    oldEntityDeclHandler = parser->m_entityDeclHandler;
    oldXmlDeclHandler = parser->m_xmlDeclHandler;
    oldDeclElementType = parser->m_declElementType;
    oldUserData = parser->m_userData;
    oldHandlerArg = parser->m_handlerArg;
    oldDefaultExpandInternalEntities = parser->m_defaultExpandInternalEntities;
    oldExternalEntityRefHandlerArg = parser->m_externalEntityRefHandlerArg;
    oldParamEntityParsing = parser->m_paramEntityParsing;
    oldInEntityValue = parser->m_prologState.inEntityValue;
    oldns_triplets = parser->m_ns_triplets;
    oldhash_secret_salt = parser->m_hash_secret_salt;
    if(context == ((const XML_Char *)NULL))
      newDtd = oldDtd;

    if(!(parser->m_ns == 0))
    {
      XML_Char tmp[2l]={ parser->m_namespaceSeparator, 0 };
      parser=parserCreate(encodingName, &parser->m_mem, tmp, newDtd);
    }

    else
      parser=parserCreate(encodingName, &parser->m_mem, ((const XML_Char *)NULL), newDtd);
    if(parser == ((XML_Parser)NULL))
      return ((XML_Parser)NULL);

    else
    {
      parser->m_startElementHandler = oldStartElementHandler;
      parser->m_endElementHandler = oldEndElementHandler;
      parser->m_characterDataHandler = oldCharacterDataHandler;
      parser->m_processingInstructionHandler = oldProcessingInstructionHandler;
      parser->m_commentHandler = oldCommentHandler;
      parser->m_startCdataSectionHandler = oldStartCdataSectionHandler;
      parser->m_endCdataSectionHandler = oldEndCdataSectionHandler;
      parser->m_defaultHandler = oldDefaultHandler;
      parser->m_unparsedEntityDeclHandler = oldUnparsedEntityDeclHandler;
      parser->m_notationDeclHandler = oldNotationDeclHandler;
      parser->m_startNamespaceDeclHandler = oldStartNamespaceDeclHandler;
      parser->m_endNamespaceDeclHandler = oldEndNamespaceDeclHandler;
      parser->m_notStandaloneHandler = oldNotStandaloneHandler;
      parser->m_externalEntityRefHandler = oldExternalEntityRefHandler;
      parser->m_skippedEntityHandler = oldSkippedEntityHandler;
      parser->m_unknownEncodingHandler = oldUnknownEncodingHandler;
      parser->m_elementDeclHandler = oldElementDeclHandler;
      parser->m_attlistDeclHandler = oldAttlistDeclHandler;
      parser->m_entityDeclHandler = oldEntityDeclHandler;
      parser->m_xmlDeclHandler = oldXmlDeclHandler;
      parser->m_declElementType = oldDeclElementType;
      parser->m_userData = oldUserData;
      if(oldUserData == oldHandlerArg)
        parser->m_handlerArg = parser->m_userData;

      else
        parser->m_handlerArg = (void *)parser;
      if(!(oldExternalEntityRefHandlerArg == oldParser))
        parser->m_externalEntityRefHandlerArg = oldExternalEntityRefHandlerArg;

      parser->m_defaultExpandInternalEntities = oldDefaultExpandInternalEntities;
      parser->m_ns_triplets = oldns_triplets;
      parser->m_hash_secret_salt = oldhash_secret_salt;
      parser->m_parentParser = oldParser;
      parser->m_paramEntityParsing = oldParamEntityParsing;
      parser->m_prologState.inEntityValue = oldInEntityValue;
      if(!(context == ((const XML_Char *)NULL)))
      {
        signed int return_value_dtdCopy=dtdCopy(oldParser, parser->m_dtd, oldDtd, &parser->m_mem);
        __CPROVER_bool tmp_if_expr;
        if(return_value_dtdCopy == 0)
          tmp_if_expr = 1;

        else
        {
          return_value_setContext=setContext(parser, context);
          tmp_if_expr = !(return_value_setContext != 0) ? 1 : 0;
        }
        if(tmp_if_expr)
        {
          XML_ParserFree(parser);
          return ((XML_Parser)NULL);
        }

        parser->m_processor = externalEntityInitProcessor;
      }

      else
      {
        parser->m_isParamEntity = 1;
        XmlPrologStateInitExternalEntity(&parser->m_prologState);
        parser->m_processor = externalParEntInitProcessor;
      }
      return parser;
    }
  }
}

// XML_FreeContentModel
// file xmlparse.c line 2307
void XML_FreeContentModel(XML_Parser parser, XML_Content *model)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_mem.free_fcn((void *)model);

}

// XML_GetBase
// file xmlparse.c line 1552
const XML_Char * XML_GetBase(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return ((const XML_Char *)NULL);

  else
    return parser->m_curBase;
}

// XML_GetBuffer
// file xmlparse.c line 2036
void * XML_GetBuffer(XML_Parser parser, signed int len)
{
  if(parser == ((XML_Parser)NULL))
    return NULL;

  else
    if(!(len >= 0))
    {
      parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
      return NULL;
    }

    else
    {
      signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
      switch(tmp_switch_value)
      {
        case 3:
        {
          parser->m_errorCode = /*enum*/XML_ERROR_SUSPENDED;
          return NULL;
        }
        case 2:
        {
          parser->m_errorCode = /*enum*/XML_ERROR_FINISHED;
          return NULL;
        }
        default:
        {
          __CPROVER_bool tmp_if_expr$15;
          if(!(parser->m_bufferLim == ((const char *)NULL)))
            tmp_if_expr$15 = parser->m_bufferEnd != ((char *)NULL) ? 1 : 0;

          else
            tmp_if_expr$15 = 0;
          signed long int tmp_if_expr$16;
          if(tmp_if_expr$15)
            tmp_if_expr$16 = parser->m_bufferLim - parser->m_bufferEnd;

          else
            tmp_if_expr$16 = 0l;
          if(!(tmp_if_expr$16 >= (signed long int)len))
          {
            signed int keep;
            signed int neededSize;
            __CPROVER_bool tmp_if_expr;
            if(!(parser->m_bufferEnd == ((char *)NULL)))
              tmp_if_expr = parser->m_bufferPtr != ((const char *)NULL) ? 1 : 0;

            else
              tmp_if_expr = 0;
            signed long int tmp_if_expr$0;
            if(tmp_if_expr)
              tmp_if_expr$0 = parser->m_bufferEnd - parser->m_bufferPtr;

            else
              tmp_if_expr$0 = 0l;
            neededSize = (signed int)((unsigned int)len + (unsigned int)tmp_if_expr$0);
            if(!(neededSize >= 0))
            {
              parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
              return NULL;
            }

            __CPROVER_bool tmp_if_expr$1;
            if(!(parser->m_bufferPtr == ((const char *)NULL)))
              tmp_if_expr$1 = parser->m_buffer != ((char *)NULL) ? 1 : 0;

            else
              tmp_if_expr$1 = 0;
            signed long int tmp_if_expr$2;
            if(tmp_if_expr$1)
              tmp_if_expr$2 = parser->m_bufferPtr - parser->m_buffer;

            else
              tmp_if_expr$2 = 0l;
            keep = (signed int)tmp_if_expr$2;
            if(keep >= 1025)
              keep = 1024;

            if(!(0x7FFFFFFF + -neededSize >= keep))
            {
              parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
              return NULL;
            }

            neededSize = neededSize + keep;
            __CPROVER_bool tmp_if_expr$13;
            if(!(parser->m_bufferLim == ((const char *)NULL)))
              tmp_if_expr$13 = parser->m_buffer != ((char *)NULL) ? 1 : 0;

            else
              tmp_if_expr$13 = 0;
            signed long int tmp_if_expr$14;
            if(tmp_if_expr$13)
              tmp_if_expr$14 = parser->m_bufferLim - parser->m_buffer;

            else
              tmp_if_expr$14 = 0l;
            if(tmp_if_expr$14 >= (signed long int)neededSize)
            {
              __CPROVER_bool tmp_if_expr$5;
              if(!(parser->m_bufferPtr == ((const char *)NULL)))
                tmp_if_expr$5 = parser->m_buffer != ((char *)NULL) ? 1 : 0;

              else
                tmp_if_expr$5 = 0;
              signed long int tmp_if_expr$6;
              if(tmp_if_expr$5)
                tmp_if_expr$6 = parser->m_bufferPtr - parser->m_buffer;

              else
                tmp_if_expr$6 = 0l;
              if(!((signed long int)keep >= tmp_if_expr$6))
              {
                signed int offset;
                __CPROVER_bool tmp_if_expr$3;
                if(!(parser->m_bufferPtr == ((const char *)NULL)))
                  tmp_if_expr$3 = parser->m_buffer != ((char *)NULL) ? 1 : 0;

                else
                  tmp_if_expr$3 = 0;
                signed long int tmp_if_expr$4;
                if(tmp_if_expr$3)
                  tmp_if_expr$4 = parser->m_bufferPtr - parser->m_buffer;

                else
                  tmp_if_expr$4 = 0l;
                offset = (signed int)tmp_if_expr$4 - keep;
                memmove((void *)parser->m_buffer, (const void *)&parser->m_buffer[(signed long int)offset], (size_t)((parser->m_bufferEnd - parser->m_bufferPtr) + (signed long int)keep));
                parser->m_bufferEnd = parser->m_bufferEnd - (signed long int)offset;
                parser->m_bufferPtr = parser->m_bufferPtr - (signed long int)offset;
              }

            }

            else
            {
              char *newBuf;
              signed int bufferSize;
              __CPROVER_bool tmp_if_expr$7;
              if(!(parser->m_bufferLim == ((const char *)NULL)))
                tmp_if_expr$7 = parser->m_bufferPtr != ((const char *)NULL) ? 1 : 0;

              else
                tmp_if_expr$7 = 0;
              signed long int tmp_if_expr$8;
              if(tmp_if_expr$7)
                tmp_if_expr$8 = parser->m_bufferLim - parser->m_bufferPtr;

              else
                tmp_if_expr$8 = 0l;
              bufferSize = (signed int)tmp_if_expr$8;
              if(bufferSize == 0)
                bufferSize = 1024;

              do
                bufferSize = (signed int)(2u * (unsigned int)bufferSize);
              while(!(bufferSize >= neededSize) && bufferSize >= 1);
              if(!(bufferSize >= 1))
              {
                parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
                return NULL;
              }

              void *return_value=parser->m_mem.malloc_fcn((size_t)bufferSize);
              newBuf = (char *)return_value;
              if(newBuf == ((char *)NULL))
              {
                parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
                return NULL;
              }

              parser->m_bufferLim = newBuf + (signed long int)bufferSize;
              if(!(parser->m_bufferPtr == ((const char *)NULL)))
              {
                __CPROVER_bool tmp_if_expr$9;
                if(!(parser->m_bufferEnd == ((char *)NULL)))
                  tmp_if_expr$9 = parser->m_bufferPtr != ((const char *)NULL) ? 1 : 0;

                else
                  tmp_if_expr$9 = 0;
                signed long int tmp_if_expr$10;
                if(tmp_if_expr$9)
                  tmp_if_expr$10 = parser->m_bufferEnd - parser->m_bufferPtr;

                else
                  tmp_if_expr$10 = 0l;
                memcpy((void *)newBuf, (const void *)&parser->m_bufferPtr[(signed long int)-keep], (size_t)(tmp_if_expr$10 + (signed long int)keep));
                parser->m_mem.free_fcn((void *)parser->m_buffer);
                parser->m_buffer = newBuf;
                __CPROVER_bool tmp_if_expr$11;
                if(!(parser->m_bufferEnd == ((char *)NULL)))
                  tmp_if_expr$11 = parser->m_bufferPtr != ((const char *)NULL) ? 1 : 0;

                else
                  tmp_if_expr$11 = 0;
                signed long int tmp_if_expr$12;
                if(tmp_if_expr$11)
                  tmp_if_expr$12 = parser->m_bufferEnd - parser->m_bufferPtr;

                else
                  tmp_if_expr$12 = 0l;
                parser->m_bufferEnd = parser->m_buffer + tmp_if_expr$12 + (signed long int)keep;
                parser->m_bufferPtr = parser->m_buffer + (signed long int)keep;
              }

              else
              {
                parser->m_bufferEnd = newBuf;
                char *tmp_assign=newBuf;
                parser->m_buffer = tmp_assign;
                parser->m_bufferPtr = tmp_assign;
              }
            }
            const char *tmp_assign$0=((const char *)NULL);
            parser->m_eventEndPtr = tmp_assign$0;
            parser->m_eventPtr = tmp_assign$0;
            parser->m_positionPtr = ((const char *)NULL);
          }

          return (void *)parser->m_bufferEnd;
        }
      }
    }
}

// XML_GetCurrentByteCount
// file xmlparse.c line 2254
signed int XML_GetCurrentByteCount(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return 0;

  else
  {
    if(!(parser->m_eventEndPtr == ((const char *)NULL)))
    {
      if(!(parser->m_eventPtr == ((const char *)NULL)))
        return (signed int)(parser->m_eventEndPtr - parser->m_eventPtr);

    }

    return 0;
  }
}

// XML_GetCurrentByteIndex
// file xmlparse.c line 2244
XML_Index XML_GetCurrentByteIndex(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return (XML_Index)-1;

  else
    if(!(parser->m_eventPtr == ((const char *)NULL)))
      return (XML_Index)(parser->m_parseEndByteIndex - (parser->m_parseEndPtr - parser->m_eventPtr));

    else
      return (XML_Index)-1;
}

// XML_GetCurrentColumnNumber
// file xmlparse.c line 2295
XML_Size XML_GetCurrentColumnNumber(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return 0ul;

  else
  {
    if(!(parser->m_eventPtr == ((const char *)NULL)))
    {
      if(parser->m_eventPtr >= parser->m_positionPtr)
      {
        parser->m_encoding->updatePosition(parser->m_encoding, parser->m_positionPtr, parser->m_eventPtr, &parser->m_position);
        parser->m_positionPtr = parser->m_eventPtr;
      }

    }

    return parser->m_position.columnNumber;
  }
}

// XML_GetCurrentLineNumber
// file xmlparse.c line 2283
XML_Size XML_GetCurrentLineNumber(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return 0ul;

  else
  {
    if(!(parser->m_eventPtr == ((const char *)NULL)))
    {
      if(parser->m_eventPtr >= parser->m_positionPtr)
      {
        parser->m_encoding->updatePosition(parser->m_encoding, parser->m_positionPtr, parser->m_eventPtr, &parser->m_position);
        parser->m_positionPtr = parser->m_eventPtr;
      }

    }

    return parser->m_position.lineNumber + 1ul;
  }
}

// XML_GetErrorCode
// file xmlparse.c line 2237
enum XML_Error XML_GetErrorCode(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_ERROR_INVALID_ARGUMENT;

  else
    return parser->m_errorCode;
}

// XML_GetFeatureList
// file xmlparse.c line 2483
const XML_Feature * XML_GetFeatureList(void)
{
  static const XML_Feature features[8l]={ { .feature=/*enum*/XML_FEATURE_SIZEOF_XML_CHAR, .name="sizeof(XML_Char)",
    .value=(signed long int)sizeof(XML_Char) /*1l*/  }, 
    { .feature=/*enum*/XML_FEATURE_SIZEOF_XML_LCHAR, .name="sizeof(XML_LChar)",
    .value=(signed long int)sizeof(XML_LChar) /*1l*/  }, 
    { .feature=/*enum*/XML_FEATURE_DTD, .name="XML_DTD", .value=0l }, 
    { .feature=/*enum*/XML_FEATURE_CONTEXT_BYTES, .name="XML_CONTEXT_BYTES",
    .value=1024l }, 
    { .feature=/*enum*/XML_FEATURE_NS, .name="XML_NS", .value=0l }, 
    { .feature=/*enum*/XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_MAXIMUM_AMPLIFICATION_DEFAULT, .name="XML_BLAP_MAX_AMP",
    .value=100l }, 
    { .feature=/*enum*/XML_FEATURE_BILLION_LAUGHS_ATTACK_PROTECTION_ACTIVATION_THRESHOLD_DEFAULT, .name="XML_BLAP_ACT_THRES",
    .value=8388608l }, 
    { .feature=/*enum*/XML_FEATURE_END, .name=((const XML_LChar *)NULL), .value=0l } };
  return features;
}

// XML_GetIdAttributeIndex
// file xmlparse.c line 1566
signed int XML_GetIdAttributeIndex(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return -1;

  else
    return parser->m_idAttIndex;
}

// XML_GetInputContext
// file xmlparse.c line 2263
const char * XML_GetInputContext(XML_Parser parser, signed int *offset, signed int *size)
{
  if(parser == ((XML_Parser)NULL))
    return ((const char *)NULL);

  else
  {
    if(!(parser->m_eventPtr == ((const char *)NULL)))
    {
      if(!(parser->m_buffer == ((char *)NULL)))
      {
        if(!(offset == ((signed int *)NULL)))
          *offset = (signed int)(parser->m_eventPtr - parser->m_buffer);

        if(!(size == ((signed int *)NULL)))
          *size = (signed int)(parser->m_bufferEnd - parser->m_buffer);

        return parser->m_buffer;
      }

    }

    return ((const char *)NULL);
  }
}

// XML_GetParsingStatus
// file xmlparse.c line 2229
void XML_GetParsingStatus(XML_Parser parser, XML_ParsingStatus *status)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    (void)sizeof(signed int) /*4ul*/ ;
    /* assertion status != NULL */
    assert(status != ((XML_ParsingStatus *)NULL));
    *status = parser->m_parsingStatus;
  }

}

// XML_GetSpecifiedAttributeCount
// file xmlparse.c line 1559
signed int XML_GetSpecifiedAttributeCount(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return -1;

  else
    return parser->m_nSpecifiedAtts;
}

// XML_MemFree
// file xmlparse.c line 2327
void XML_MemFree(XML_Parser parser, void *ptr)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_mem.free_fcn(ptr);

}

// XML_MemMalloc
// file xmlparse.c line 2313
void * XML_MemMalloc(XML_Parser parser, size_t size)
{
  if(parser == ((XML_Parser)NULL))
    return NULL;

  else
  {
    void *return_value=parser->m_mem.malloc_fcn(size);
    return return_value;
  }
}

// XML_MemRealloc
// file xmlparse.c line 2320
void * XML_MemRealloc(XML_Parser parser, void *ptr, size_t size)
{
  if(parser == ((XML_Parser)NULL))
    return NULL;

  else
  {
    void *return_value=parser->m_mem.realloc_fcn(ptr, size);
    return return_value;
  }
}

// XML_Parse
// file xmlparse.c line 1817
enum XML_Status XML_Parse(XML_Parser parser, const char *s, signed int len, signed int isFinal)
{
  XML_Bool return_value_startParsing;
  void *buff;
  void *return_value_XML_GetBuffer;
  if(parser == ((XML_Parser)NULL) || !(len >= 0) || s == ((const char *)NULL) && !(len == 0))
  {
    if(!(parser == ((XML_Parser)NULL)))
      parser->m_errorCode = /*enum*/XML_ERROR_INVALID_ARGUMENT;

    return /*enum*/XML_STATUS_ERROR;
  }

  else
  {
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    switch(tmp_switch_value)
    {
      case 3:
      {
        parser->m_errorCode = /*enum*/XML_ERROR_SUSPENDED;
        return /*enum*/XML_STATUS_ERROR;
      }
      case 2:
      {
        parser->m_errorCode = /*enum*/XML_ERROR_FINISHED;
        return /*enum*/XML_STATUS_ERROR;
      }
      case 0:
        if(parser->m_parentParser == ((XML_Parser)NULL))
        {
          return_value_startParsing=startParsing(parser);
          if(return_value_startParsing == 0)
          {
            parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
            return /*enum*/XML_STATUS_ERROR;
          }

        }

      default:
      {
        parser->m_parsingStatus.parsing = /*enum*/XML_PARSING;
        if(len == 0)
        {
          parser->m_parsingStatus.finalBuffer = (XML_Bool)isFinal;
          if(isFinal == 0)
            return /*enum*/XML_STATUS_OK;

          parser->m_positionPtr = parser->m_bufferPtr;
          parser->m_parseEndPtr = parser->m_bufferEnd;
          enum XML_Error return_value=parser->m_processor(parser, parser->m_bufferPtr, parser->m_parseEndPtr, &parser->m_bufferPtr);
          parser->m_errorCode = return_value;
          if((signed int)parser->m_errorCode == 0)
          {
            signed int tmp_switch_value$0=(signed int)parser->m_parsingStatus.parsing;
            if(tmp_switch_value$0 == 3)
            {
              parser->m_encoding->updatePosition(parser->m_encoding, parser->m_positionPtr, parser->m_bufferPtr, &parser->m_position);
              parser->m_positionPtr = parser->m_bufferPtr;
              return /*enum*/XML_STATUS_SUSPENDED;
              parser->m_parsingStatus.parsing = /*enum*/XML_FINISHED;
            }

            return /*enum*/XML_STATUS_OK;
          }

          parser->m_eventEndPtr = parser->m_eventPtr;
          parser->m_processor = errorProcessor;
          return /*enum*/XML_STATUS_ERROR;
        }

        return_value_XML_GetBuffer=XML_GetBuffer(parser, len);
        buff = return_value_XML_GetBuffer;
        if(buff == NULL)
          return /*enum*/XML_STATUS_ERROR;

        else
        {
          memcpy(buff, (const void *)s, (size_t)len);
          enum XML_Status return_value_XML_ParseBuffer=XML_ParseBuffer(parser, len, isFinal);
          return return_value_XML_ParseBuffer;
        }
      }
    }
  }
}

// XML_ParseBuffer
// file xmlparse.c line 1971
enum XML_Status XML_ParseBuffer(XML_Parser parser, signed int len, signed int isFinal)
{
  const char *start;
  enum XML_Status result=/*enum*/XML_STATUS_OK;
  XML_Bool return_value_startParsing;
  enum XML_Error return_value;
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_STATUS_ERROR;

  else
  {
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    switch(tmp_switch_value)
    {
      case 3:
      {
        parser->m_errorCode = /*enum*/XML_ERROR_SUSPENDED;
        return /*enum*/XML_STATUS_ERROR;
      }
      case 2:
      {
        parser->m_errorCode = /*enum*/XML_ERROR_FINISHED;
        return /*enum*/XML_STATUS_ERROR;
      }
      case 0:
      {
        if(parser->m_bufferPtr == ((const char *)NULL))
        {
          parser->m_errorCode = /*enum*/XML_ERROR_NO_BUFFER;
          return /*enum*/XML_STATUS_ERROR;
        }

        if(parser->m_parentParser == ((XML_Parser)NULL))
        {
          return_value_startParsing=startParsing(parser);
          if(return_value_startParsing == 0)
          {
            parser->m_errorCode = /*enum*/XML_ERROR_NO_MEMORY;
            return /*enum*/XML_STATUS_ERROR;
          }

        }

      }
      default:
      {
        parser->m_parsingStatus.parsing = /*enum*/XML_PARSING;
        start = parser->m_bufferPtr;
        parser->m_positionPtr = start;
        parser->m_bufferEnd = parser->m_bufferEnd + (signed long int)len;
        parser->m_parseEndPtr = parser->m_bufferEnd;
        parser->m_parseEndByteIndex = parser->m_parseEndByteIndex + (signed long int)len;
        parser->m_parsingStatus.finalBuffer = (XML_Bool)isFinal;
        return_value=parser->m_processor(parser, start, parser->m_parseEndPtr, &parser->m_bufferPtr);
      }
    }
    parser->m_errorCode = return_value;
    if(!((signed int)parser->m_errorCode == 0))
    {
      parser->m_eventEndPtr = parser->m_eventPtr;
      parser->m_processor = errorProcessor;
      return /*enum*/XML_STATUS_ERROR;
    }

    else
    {
      signed int tmp_switch_value$0=(signed int)parser->m_parsingStatus.parsing;
      if(tmp_switch_value$0 == 3)
      {
        result = /*enum*/XML_STATUS_SUSPENDED;
        if(!(isFinal == 0))
        {
          parser->m_parsingStatus.parsing = /*enum*/XML_FINISHED;
          return result;
        }

      }

    }
    parser->m_encoding->updatePosition(parser->m_encoding, parser->m_positionPtr, parser->m_bufferPtr, &parser->m_position);
    parser->m_positionPtr = parser->m_bufferPtr;
    return result;
  }
}

// XML_ParserCreate
// file xmlparse.c line 715
XML_Parser XML_ParserCreate(const XML_Char *encodingName)
{
  XML_Parser return_value_XML_ParserCreate_MM=XML_ParserCreate_MM(encodingName, ((const XML_Memory_Handling_Suite *)NULL), ((const XML_Char *)NULL));
  return return_value_XML_ParserCreate_MM;
}

// XML_ParserCreateNS
// file xmlparse.c line 720
XML_Parser XML_ParserCreateNS(const XML_Char *encodingName, XML_Char nsSep)
{
  XML_Char tmp[2l]={ nsSep, 0 };
  XML_Parser return_value_XML_ParserCreate_MM=XML_ParserCreate_MM(encodingName, ((const XML_Memory_Handling_Suite *)NULL), tmp);
  return return_value_XML_ParserCreate_MM;
}

// XML_ParserCreate_MM
// file xmlparse.c line 963
XML_Parser XML_ParserCreate_MM(const XML_Char *encodingName, const XML_Memory_Handling_Suite *memsuite, const XML_Char *nameSep)
{
  XML_Parser return_value_parserCreate=parserCreate(encodingName, memsuite, nameSep, ((DTD *)NULL));
  return return_value_parserCreate;
}

// XML_ParserFree
// file xmlparse.c line 1428
void XML_ParserFree(XML_Parser parser)
{
  TAG *tagList;
  OPEN_INTERNAL_ENTITY *entityList;
  if(!(parser == ((XML_Parser)NULL)))
  {
    tagList = parser->m_tagStack;
    {
      TAG *p;
      if(tagList == ((TAG *)NULL))
      {
        if(parser->m_freeTagList == ((TAG *)NULL))
          goto __CPROVER_DUMP_L5;

        tagList = parser->m_freeTagList;
        parser->m_freeTagList = ((TAG *)NULL);
      }

      p = tagList;
      tagList = tagList->parent;
      parser->m_mem.free_fcn((void *)p->buf);
      destroyBindings(p->bindings, parser);
      parser->m_mem.free_fcn((void *)p);
    }

  __CPROVER_DUMP_L5:
    ;
    entityList = parser->m_openInternalEntities;
    {
      OPEN_INTERNAL_ENTITY *openEntity;
      if(entityList == ((OPEN_INTERNAL_ENTITY *)NULL))
      {
        if(parser->m_freeInternalEntities == ((OPEN_INTERNAL_ENTITY *)NULL))
          goto __CPROVER_DUMP_L9;

        entityList = parser->m_freeInternalEntities;
        parser->m_freeInternalEntities = ((OPEN_INTERNAL_ENTITY *)NULL);
      }

      openEntity = entityList;
      entityList = entityList->next;
      parser->m_mem.free_fcn((void *)openEntity);
    }

  __CPROVER_DUMP_L9:
    ;
    destroyBindings(parser->m_freeBindingList, parser);
    destroyBindings(parser->m_inheritedBindings, parser);
    poolDestroy(&parser->m_tempPool);
    poolDestroy(&parser->m_temp2Pool);
    parser->m_mem.free_fcn((void *)parser->m_protocolEncodingName);
    if(parser->m_isParamEntity == 0)
    {
      if(!(parser->m_dtd == ((DTD *)NULL)))
        dtdDestroy(parser->m_dtd, (XML_Bool)!(parser->m_parentParser != ((XML_Parser)NULL)), &parser->m_mem);

    }

    parser->m_mem.free_fcn((void *)parser->m_atts);
    parser->m_mem.free_fcn((void *)parser->m_groupConnector);
    parser->m_mem.free_fcn((void *)parser->m_buffer);
    parser->m_mem.free_fcn((void *)parser->m_dataBuf);
    parser->m_mem.free_fcn((void *)parser->m_nsAtts);
    parser->m_mem.free_fcn(parser->m_unknownEncodingMem);
    if(!(parser->m_unknownEncodingRelease == ((void (*)(void *))NULL)))
      parser->m_unknownEncodingRelease(parser->m_unknownEncodingData);

    parser->m_mem.free_fcn((void *)parser);
  }

}

// XML_ParserReset
// file xmlparse.c line 1180
XML_Bool XML_ParserReset(XML_Parser parser, const XML_Char *encodingName)
{
  TAG *tStk;
  OPEN_INTERNAL_ENTITY *openEntityList;
  if(parser == ((XML_Parser)NULL))
    return 0;

  else
    if(!(parser->m_parentParser == ((XML_Parser)NULL)))
      return 0;

    else
    {
      tStk = parser->m_tagStack;
      while(!(tStk == ((TAG *)NULL)))
      {
        TAG *tag=tStk;
        tStk = tStk->parent;
        tag->parent = parser->m_freeTagList;
        moveToFreeBindingList(parser, tag->bindings);
        tag->bindings = ((BINDING *)NULL);
        parser->m_freeTagList = tag;
      }
      openEntityList = parser->m_openInternalEntities;
      while(!(openEntityList == ((OPEN_INTERNAL_ENTITY *)NULL)))
      {
        OPEN_INTERNAL_ENTITY *openEntity=openEntityList;
        openEntityList = openEntity->next;
        openEntity->next = parser->m_freeInternalEntities;
        parser->m_freeInternalEntities = openEntity;
      }
      moveToFreeBindingList(parser, parser->m_inheritedBindings);
      parser->m_mem.free_fcn(parser->m_unknownEncodingMem);
      if(!(parser->m_unknownEncodingRelease == ((void (*)(void *))NULL)))
        parser->m_unknownEncodingRelease(parser->m_unknownEncodingData);

      poolClear(&parser->m_tempPool);
      poolClear(&parser->m_temp2Pool);
      parser->m_mem.free_fcn((void *)parser->m_protocolEncodingName);
      parser->m_protocolEncodingName = ((const XML_Char *)NULL);
      parserInit(parser, encodingName);
      dtdReset(parser->m_dtd, &parser->m_mem);
      return 1;
    }
}

// XML_ResumeParser
// file xmlparse.c line 2189
enum XML_Status XML_ResumeParser(XML_Parser parser)
{
  enum XML_Status result=/*enum*/XML_STATUS_OK;
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_STATUS_ERROR;

  else
    if(!((signed int)parser->m_parsingStatus.parsing == 3))
    {
      parser->m_errorCode = /*enum*/XML_ERROR_NOT_SUSPENDED;
      return /*enum*/XML_STATUS_ERROR;
    }

    else
    {
      parser->m_parsingStatus.parsing = /*enum*/XML_PARSING;
      enum XML_Error return_value=parser->m_processor(parser, parser->m_bufferPtr, parser->m_parseEndPtr, &parser->m_bufferPtr);
      parser->m_errorCode = return_value;
      if(!((signed int)parser->m_errorCode == 0))
      {
        parser->m_eventEndPtr = parser->m_eventPtr;
        parser->m_processor = errorProcessor;
        return /*enum*/XML_STATUS_ERROR;
      }

      else
      {
        signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
        if(tmp_switch_value == 3)
        {
          result = /*enum*/XML_STATUS_SUSPENDED;
          if(!(parser->m_parsingStatus.finalBuffer == 0))
          {
            parser->m_parsingStatus.parsing = /*enum*/XML_FINISHED;
            return result;
          }

        }

      }
      parser->m_encoding->updatePosition(parser->m_encoding, parser->m_positionPtr, parser->m_bufferPtr, &parser->m_position);
      parser->m_positionPtr = parser->m_bufferPtr;
      return result;
    }
}

// XML_SetAttlistDeclHandler
// file xmlparse.c line 1768
void XML_SetAttlistDeclHandler(XML_Parser parser, XML_AttlistDeclHandler attdecl)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_attlistDeclHandler = attdecl;

}

// XML_SetBase
// file xmlparse.c line 1538
enum XML_Status XML_SetBase(XML_Parser parser, const XML_Char *p)
{
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_STATUS_ERROR;

  else
  {
    if(!(p == ((const XML_Char *)NULL)))
    {
      p=poolCopyString(&parser->m_dtd->pool, p);
      if(p == ((const XML_Char *)NULL))
        return /*enum*/XML_STATUS_ERROR;

      parser->m_curBase = p;
    }

    else
      parser->m_curBase = ((const XML_Char *)NULL);
    return /*enum*/XML_STATUS_OK;
  }
}

// XML_SetBillionLaughsAttackProtectionActivationThreshold
// file xmlparse.c line 2543
XML_Bool XML_SetBillionLaughsAttackProtectionActivationThreshold(XML_Parser parser, unsigned long long int activationThresholdBytes)
{
  __CPROVER_bool tmp_if_expr;
  if(parser == ((XML_Parser)NULL))
    tmp_if_expr = 1;

  else
    tmp_if_expr = parser->m_parentParser != ((XML_Parser)NULL) ? 1 : 0;
  if(tmp_if_expr)
    return 0;

  else
  {
    parser->m_accounting.activationThresholdBytes = activationThresholdBytes;
    return 1;
  }
}

// XML_SetBillionLaughsAttackProtectionMaximumAmplification
// file xmlparse.c line 2531
XML_Bool XML_SetBillionLaughsAttackProtectionMaximumAmplification(XML_Parser parser, float maximumAmplificationFactor)
{
  __CPROVER_bool tmp_if_expr;
  if(parser == ((XML_Parser)NULL))
    tmp_if_expr = 1;

  else
    tmp_if_expr = parser->m_parentParser != ((XML_Parser)NULL) ? 1 : 0;
  if(tmp_if_expr || isnan((double)maximumAmplificationFactor) || maximumAmplificationFactor < 1.0f)
    return 0;

  else
  {
    parser->m_accounting.maximumAmplificationFactor = maximumAmplificationFactor;
    return 1;
  }
}

// XML_SetCdataSectionHandler
// file xmlparse.c line 1623
void XML_SetCdataSectionHandler(XML_Parser parser, XML_StartCdataSectionHandler start, XML_EndCdataSectionHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_startCdataSectionHandler = start;
    parser->m_endCdataSectionHandler = end;
  }

}

// XML_SetCharacterDataHandler
// file xmlparse.c line 1603
void XML_SetCharacterDataHandler(XML_Parser parser, XML_CharacterDataHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_characterDataHandler = handler;

}

// XML_SetCommentHandler
// file xmlparse.c line 1617
void XML_SetCommentHandler(XML_Parser parser, XML_CommentHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_commentHandler = handler;

}

// XML_SetDefaultHandler
// file xmlparse.c line 1647
void XML_SetDefaultHandler(XML_Parser parser, XML_DefaultHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_defaultHandler = handler;
    parser->m_defaultExpandInternalEntities = 0;
  }

}

// XML_SetDefaultHandlerExpand
// file xmlparse.c line 1655
void XML_SetDefaultHandlerExpand(XML_Parser parser, XML_DefaultHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_defaultHandler = handler;
    parser->m_defaultExpandInternalEntities = 1;
  }

}

// XML_SetDoctypeDeclHandler
// file xmlparse.c line 1663
void XML_SetDoctypeDeclHandler(XML_Parser parser, XML_StartDoctypeDeclHandler start, XML_EndDoctypeDeclHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_startDoctypeDeclHandler = start;
    parser->m_endDoctypeDeclHandler = end;
  }

}

// XML_SetElementDeclHandler
// file xmlparse.c line 1762
void XML_SetElementDeclHandler(XML_Parser parser, XML_ElementDeclHandler eldecl)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_elementDeclHandler = eldecl;

}

// XML_SetElementHandler
// file xmlparse.c line 1582
void XML_SetElementHandler(XML_Parser parser, XML_StartElementHandler start, XML_EndElementHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_startElementHandler = start;
    parser->m_endElementHandler = end;
  }

}

// XML_SetEncoding
// file xmlparse.c line 1221
enum XML_Status XML_SetEncoding(XML_Parser parser, const XML_Char *encodingName)
{
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_STATUS_ERROR;

  else
  {
    __CPROVER_bool tmp_if_expr;
    if((signed int)parser->m_parsingStatus.parsing == 1)
      tmp_if_expr = 1;

    else
      tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;
    if(tmp_if_expr)
      return /*enum*/XML_STATUS_ERROR;

    else
    {
      parser->m_mem.free_fcn((void *)parser->m_protocolEncodingName);
      if(encodingName == ((const XML_Char *)NULL))
        parser->m_protocolEncodingName = ((const XML_Char *)NULL);

      else
      {
        XML_Char *return_value_copyString=copyString(encodingName, &parser->m_mem);
        parser->m_protocolEncodingName = return_value_copyString;
        if(parser->m_protocolEncodingName == ((const XML_Char *)NULL))
          return /*enum*/XML_STATUS_ERROR;

      }
      return /*enum*/XML_STATUS_OK;
    }
  }
}

// XML_SetEndCdataSectionHandler
// file xmlparse.c line 1640
void XML_SetEndCdataSectionHandler(XML_Parser parser, XML_EndCdataSectionHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_endCdataSectionHandler = end;

}

// XML_SetEndDoctypeDeclHandler
// file xmlparse.c line 1679
void XML_SetEndDoctypeDeclHandler(XML_Parser parser, XML_EndDoctypeDeclHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_endDoctypeDeclHandler = end;

}

// XML_SetEndElementHandler
// file xmlparse.c line 1597
void XML_SetEndElementHandler(XML_Parser parser, XML_EndElementHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_endElementHandler = end;

}

// XML_SetEndNamespaceDeclHandler
// file xmlparse.c line 1715
void XML_SetEndNamespaceDeclHandler(XML_Parser parser, XML_EndNamespaceDeclHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_endNamespaceDeclHandler = end;

}

// XML_SetEntityDeclHandler
// file xmlparse.c line 1774
void XML_SetEntityDeclHandler(XML_Parser parser, XML_EntityDeclHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_entityDeclHandler = handler;

}

// XML_SetExternalEntityRefHandler
// file xmlparse.c line 1729
void XML_SetExternalEntityRefHandler(XML_Parser parser, XML_ExternalEntityRefHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_externalEntityRefHandler = handler;

}

// XML_SetExternalEntityRefHandlerArg
// file xmlparse.c line 1736
void XML_SetExternalEntityRefHandlerArg(XML_Parser parser, void *arg)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    if(!(arg == NULL))
      parser->m_externalEntityRefHandlerArg = (XML_Parser)arg;

    else
      parser->m_externalEntityRefHandlerArg = parser;
  }

}

// XML_SetHashSalt
// file xmlparse.c line 1803
signed int XML_SetHashSalt(XML_Parser parser, unsigned long int hash_salt)
{
  signed int return_value_XML_SetHashSalt;
  if(parser == ((XML_Parser)NULL))
    return 0;

  else
    if(!(parser->m_parentParser == ((XML_Parser)NULL)))
    {
      return_value_XML_SetHashSalt=XML_SetHashSalt(parser->m_parentParser, hash_salt);
      return return_value_XML_SetHashSalt;
    }

    else
    {
      __CPROVER_bool tmp_if_expr;
      if((signed int)parser->m_parsingStatus.parsing == 1)
        tmp_if_expr = 1;

      else
        tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;
      if(tmp_if_expr)
        return 0;

      else
      {
        parser->m_hash_secret_salt = hash_salt;
        return 1;
      }
    }
}

// XML_SetNamespaceDeclHandler
// file xmlparse.c line 1698
void XML_SetNamespaceDeclHandler(XML_Parser parser, XML_StartNamespaceDeclHandler start, XML_EndNamespaceDeclHandler end)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_startNamespaceDeclHandler = start;
    parser->m_endNamespaceDeclHandler = end;
  }

}

// XML_SetNotStandaloneHandler
// file xmlparse.c line 1722
void XML_SetNotStandaloneHandler(XML_Parser parser, XML_NotStandaloneHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_notStandaloneHandler = handler;

}

// XML_SetNotationDeclHandler
// file xmlparse.c line 1692
void XML_SetNotationDeclHandler(XML_Parser parser, XML_NotationDeclHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_notationDeclHandler = handler;

}

// XML_SetParamEntityParsing
// file xmlparse.c line 1786
signed int XML_SetParamEntityParsing(XML_Parser parser, enum XML_ParamEntityParsing peParsing)
{
  if(parser == ((XML_Parser)NULL))
    return 0;

  else
  {
    __CPROVER_bool tmp_if_expr;
    if((signed int)parser->m_parsingStatus.parsing == 1)
      tmp_if_expr = 1;

    else
      tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;
    if(tmp_if_expr)
      return 0;

    else
    {
      parser->m_paramEntityParsing = peParsing;
      return 1;
    }
  }
}

// XML_SetProcessingInstructionHandler
// file xmlparse.c line 1610
void XML_SetProcessingInstructionHandler(XML_Parser parser, XML_ProcessingInstructionHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_processingInstructionHandler = handler;

}

// XML_SetReturnNSTriplet
// file xmlparse.c line 1517
void XML_SetReturnNSTriplet(XML_Parser parser, signed int do_nst)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    __CPROVER_bool tmp_if_expr;
    if((signed int)parser->m_parsingStatus.parsing == 1)
      tmp_if_expr = 1;

    else
      tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;
    if(!tmp_if_expr)
      parser->m_ns_triplets = do_nst != 0 ? 1 : 0;

  }

}

// XML_SetSkippedEntityHandler
// file xmlparse.c line 1746
void XML_SetSkippedEntityHandler(XML_Parser parser, XML_SkippedEntityHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_skippedEntityHandler = handler;

}

// XML_SetStartCdataSectionHandler
// file xmlparse.c line 1633
void XML_SetStartCdataSectionHandler(XML_Parser parser, XML_StartCdataSectionHandler start)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_startCdataSectionHandler = start;

}

// XML_SetStartDoctypeDeclHandler
// file xmlparse.c line 1672
void XML_SetStartDoctypeDeclHandler(XML_Parser parser, XML_StartDoctypeDeclHandler start)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_startDoctypeDeclHandler = start;

}

// XML_SetStartElementHandler
// file xmlparse.c line 1591
void XML_SetStartElementHandler(XML_Parser parser, XML_StartElementHandler start)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_startElementHandler = start;

}

// XML_SetStartNamespaceDeclHandler
// file xmlparse.c line 1708
void XML_SetStartNamespaceDeclHandler(XML_Parser parser, XML_StartNamespaceDeclHandler start)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_startNamespaceDeclHandler = start;

}

// XML_SetUnknownEncodingHandler
// file xmlparse.c line 1753
void XML_SetUnknownEncodingHandler(XML_Parser parser, XML_UnknownEncodingHandler handler, void *data)
{
  if(!(parser == ((XML_Parser)NULL)))
  {
    parser->m_unknownEncodingHandler = handler;
    parser->m_unknownEncodingHandlerData = data;
  }

}

// XML_SetUnparsedEntityDeclHandler
// file xmlparse.c line 1685
void XML_SetUnparsedEntityDeclHandler(XML_Parser parser, XML_UnparsedEntityDeclHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_unparsedEntityDeclHandler = handler;

}

// XML_SetUserData
// file xmlparse.c line 1528
void XML_SetUserData(XML_Parser parser, void *p)
{
  void *tmp_assign;
  if(!(parser == ((XML_Parser)NULL)))
  {
    if(parser->m_handlerArg == parser->m_userData)
    {
      tmp_assign = p;
      parser->m_userData = tmp_assign;
      parser->m_handlerArg = tmp_assign;
    }

    else
      parser->m_userData = p;
  }

}

// XML_SetXmlDeclHandler
// file xmlparse.c line 1780
void XML_SetXmlDeclHandler(XML_Parser parser, XML_XmlDeclHandler handler)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_xmlDeclHandler = handler;

}

// XML_StopParser
// file xmlparse.c line 2159
enum XML_Status XML_StopParser(XML_Parser parser, XML_Bool resumable)
{
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_STATUS_ERROR;

  else
  {
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    switch(tmp_switch_value)
    {
      case 3:
      {
        if(!(resumable == 0))
        {
          parser->m_errorCode = /*enum*/XML_ERROR_SUSPENDED;
          return /*enum*/XML_STATUS_ERROR;
        }

        parser->m_parsingStatus.parsing = /*enum*/XML_FINISHED;
        break;
      }
      case 2:
      {
        parser->m_errorCode = /*enum*/XML_ERROR_FINISHED;
        return /*enum*/XML_STATUS_ERROR;
      }
      default:
        if(!(resumable == 0))
        {
          if(!(parser->m_isParamEntity == 0))
          {
            parser->m_errorCode = /*enum*/XML_ERROR_SUSPEND_PE;
            return /*enum*/XML_STATUS_ERROR;
          }

          parser->m_parsingStatus.parsing = /*enum*/XML_SUSPENDED;
        }

        else
          parser->m_parsingStatus.parsing = /*enum*/XML_FINISHED;
    }
    return /*enum*/XML_STATUS_OK;
  }
}

// XML_UseForeignDTD
// file xmlparse.c line 1500
enum XML_Error XML_UseForeignDTD(XML_Parser parser, XML_Bool useDTD)
{
  if(parser == ((XML_Parser)NULL))
    return /*enum*/XML_ERROR_INVALID_ARGUMENT;

  else
  {
    __CPROVER_bool tmp_if_expr;
    if((signed int)parser->m_parsingStatus.parsing == 1)
      tmp_if_expr = 1;

    else
      tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;
    if(tmp_if_expr)
      return /*enum*/XML_ERROR_CANT_CHANGE_FEATURE_ONCE_PARSING;

    else
    {
      parser->m_useForeignDTD = useDTD;
      return /*enum*/XML_ERROR_NONE;
    }
  }
}

// XML_UseParserAsHandlerArg
// file xmlparse.c line 1494
void XML_UseParserAsHandlerArg(XML_Parser parser)
{
  if(!(parser == ((XML_Parser)NULL)))
    parser->m_handlerArg = (void *)parser;

}

// accountingDiffTolerated
// file xmlparse.c line 7568
static XML_Bool accountingDiffTolerated(XML_Parser originParser, signed int tok, const char *before, const char *after, signed int source_line, enum XML_Account account)
{
  if(tok == -4 || tok == -2 || tok == -1 || tok == 0)
    return 1;

  else
    if((signed int)account == 2)
      return 1;

    else
    {
      unsigned int levelsAwayFromRootParser;
      XML_Parser rootParser;
      XML_Parser return_value_getRootParserOf=getRootParserOf(originParser, &levelsAwayFromRootParser);
      rootParser = return_value_getRootParserOf;
      (void)sizeof(signed int) /*4ul*/ ;
      /* assertion ! rootParser->m_parentParser */
      assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
      const signed int isDirect=(const signed int)((signed int)account == 0 && originParser == rootParser);
      const ptrdiff_t bytesMore=after - before;
      XmlBigCount *additionTarget;
      XmlBigCount *tmp_if_expr;
      if(!(isDirect == 0))
        tmp_if_expr = &rootParser->m_accounting.countBytesDirect;

      else
        tmp_if_expr = &rootParser->m_accounting.countBytesIndirect;
      additionTarget = tmp_if_expr;
      if(!(18446744073709551615ull + -((XmlBigCount)bytesMore) >= *additionTarget))
        return 0;

      else
      {
        *additionTarget = *additionTarget + (unsigned long int)bytesMore;
        const XmlBigCount countBytesOutput=rootParser->m_accounting.countBytesDirect + rootParser->m_accounting.countBytesIndirect;
        float amplificationFactor;
        float return_value_accountingGetCurrentAmplification=accountingGetCurrentAmplification(rootParser);
        amplificationFactor = return_value_accountingGetCurrentAmplification;
        XML_Bool tolerated;
        __CPROVER_bool tmp_if_expr$0;
        if(!(countBytesOutput >= rootParser->m_accounting.activationThresholdBytes))
          tmp_if_expr$0 = 1;

        else
          tmp_if_expr$0 = amplificationFactor <= rootParser->m_accounting.maximumAmplificationFactor ? 1 : 0;
        tolerated = (const XML_Bool)tmp_if_expr$0;
        if(rootParser->m_accounting.debugLevel >= 2)
        {
          accountingReportStats(rootParser, "");
          accountingReportDiff(rootParser, levelsAwayFromRootParser, before, after, bytesMore, source_line, account);
        }

        return tolerated;
      }
    }
}

// accountingGetCurrentAmplification
// file xmlparse.c line 7493
static float accountingGetCurrentAmplification(XML_Parser rootParser)
{
  const XmlBigCount countBytesOutput=rootParser->m_accounting.countBytesDirect + rootParser->m_accounting.countBytesIndirect;
  float amplificationFactor;
  float tmp_if_expr;
  if(!(rootParser->m_accounting.countBytesDirect == 0ull))
    tmp_if_expr = (float)countBytesOutput / (float)rootParser->m_accounting.countBytesDirect;

  else
    tmp_if_expr = 1.0f;
  amplificationFactor = tmp_if_expr;
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  return amplificationFactor;
}

// accountingOnAbort
// file xmlparse.c line 7526
static void accountingOnAbort(XML_Parser originParser)
{
  accountingReportStats(originParser, " ABORTING\n");
}

// accountingReportDiff
// file xmlparse.c line 7531
static void accountingReportDiff(XML_Parser rootParser, unsigned int levelsAwayFromRootParser, const char *before, const char *after, ptrdiff_t bytesMore, signed int source_line, enum XML_Account account)
{
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  fprintf(stderr, " (+%6ld bytes %s|%d, xmlparse.c:%d) %*s\"", bytesMore, (signed int)account == 0 ? "DIR" : "EXP", levelsAwayFromRootParser, source_line, 10, (const void *)"");
  const char ellipis[5l]={ '[', '.', '.', ']', 0 };
  const size_t ellipsisLength=sizeof(const char [5l]) /*5ul*/  - 1ul;
  const unsigned int contextLength=10u;
  const char *walker=before;
  if(rootParser->m_accounting.debugLevel >= 3 || (ptrdiff_t)(unsigned long int)contextLength + (ptrdiff_t)ellipsisLength + (ptrdiff_t)(unsigned long int)contextLength >= after - before)
    for( ; walker < after; walker = walker + 1l)
    {
      const char *return_value_unsignedCharToPrintable=unsignedCharToPrintable((unsigned char)walker[0l]);
      fprintf(stderr, "%s", return_value_unsignedCharToPrintable);
    }

  else
  {
    for( ; walker < before + (signed long int)contextLength; walker = walker + 1l)
    {
      const char *return_value_unsignedCharToPrintable$0=unsignedCharToPrintable((unsigned char)walker[0l]);
      fprintf(stderr, "%s", return_value_unsignedCharToPrintable$0);
    }
    fprintf(stderr, ellipis);
    walker = after - (signed long int)contextLength;
    for( ; walker < after; walker = walker + 1l)
    {
      const char *return_value_unsignedCharToPrintable$1=unsignedCharToPrintable((unsigned char)walker[0l]);
      fprintf(stderr, "%s", return_value_unsignedCharToPrintable$1);
    }
  }
  fprintf(stderr, "\"\n");
}

// accountingReportStats
// file xmlparse.c line 7507
static void accountingReportStats(XML_Parser originParser, const char *epilog)
{
  XML_Parser rootParser;
  XML_Parser return_value_getRootParserOf=getRootParserOf(originParser, ((unsigned int *)NULL));
  rootParser = return_value_getRootParserOf;
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  if(rootParser->m_accounting.debugLevel >= 1)
  {
    float amplificationFactor;
    float return_value_accountingGetCurrentAmplification=accountingGetCurrentAmplification(rootParser);
    amplificationFactor = return_value_accountingGetCurrentAmplification;
    fprintf(stderr, "expat: Accounting(%p): Direct %10llu, indirect %10llu, amplification %8.2f%s", (void *)rootParser, rootParser->m_accounting.countBytesDirect, rootParser->m_accounting.countBytesIndirect, (double)amplificationFactor, epilog);
  }

}

// addBinding
// file xmlparse.c line 3711
static enum XML_Error addBinding(XML_Parser parser, PREFIX *prefix, const ATTRIBUTE_ID *attId, const XML_Char *uri, BINDING **bindingsPtr)
{
  XML_Bool mustBeXML=0;
  XML_Bool isXML=1;
  XML_Bool isXMLNS=1;
  BINDING *b;
  signed int len;
  if((signed int)*uri == 0)
  {
    if(!(prefix->name == ((const XML_Char *)NULL)))
      return /*enum*/XML_ERROR_UNDECLARING_PREFIX;

  }

  if(!(prefix->name == ((const XML_Char *)NULL)))
  {
    if((signed int)*prefix->name == 0x78)
    {
      if((signed int)prefix->name[1l] == 0x6D)
      {
        if((signed int)prefix->name[2l] == 0x6C)
        {
          if((signed int)prefix->name[3l] == 0x6E)
          {
            if((signed int)prefix->name[4l] == 0x73)
            {
              if((signed int)prefix->name[5l] == 0)
                return /*enum*/XML_ERROR_RESERVED_PREFIX_XMLNS;

            }

          }

          if((signed int)prefix->name[3l] == 0)
            mustBeXML = 1;

        }

      }

    }

  }

  len = 0;
  __CPROVER_bool tmp_if_expr;
  __CPROVER_bool tmp_if_expr$0;
  static const signed int xmlnsLen=(const signed int)(sizeof(const XML_Char [30l]) /*30ul*/  / sizeof(XML_Char) /*1ul*/  - 1ul);
  static const signed int xmlLen=(const signed int)(sizeof(const XML_Char [37l]) /*37ul*/  / sizeof(XML_Char) /*1ul*/  - 1ul);
  for( ; !(uri[(signed long int)len] == 0); len = len + 1)
  {
    if(!(isXML == 0))
    {
      static const XML_Char xmlNamespace[37l]={ 'h', 't', 't', 'p', ':', '/', '/', 'w', 'w', 'w', '.', 'w', '3', '.', 'o', 'r', 'g', '/', 'X', 'M', 'L', '/', '1', '9', '9', '8', '/', 'n', 'a', 'm', 'e', 's', 'p', 'a', 'c', 'e', 0 };
      if(!(xmlLen >= len))
        tmp_if_expr = 1;

      else
        tmp_if_expr = uri[(signed long int)len] != xmlNamespace[(signed long int)len] ? 1 : 0;
      if(tmp_if_expr)
        isXML = 0;

    }

    if(mustBeXML == 0 && !(isXMLNS == 0))
    {
      static const XML_Char xmlnsNamespace[30l]={ 'h', 't', 't', 'p', ':', '/', '/', 'w', 'w', 'w', '.', 'w', '3', '.', 'o', 'r', 'g', '/', '2', '0', '0', '0', '/', 'x', 'm', 'l', 'n', 's', '/', 0 };
      if(!(xmlnsLen >= len))
        tmp_if_expr$0 = 1;

      else
        tmp_if_expr$0 = uri[(signed long int)len] != xmlnsNamespace[(signed long int)len] ? 1 : 0;
      if(tmp_if_expr$0)
        isXMLNS = 0;

    }

    if(!(parser->m_ns == 0))
    {
      if(uri[(signed long int)len] == parser->m_namespaceSeparator)
        return /*enum*/XML_ERROR_SYNTAX;

    }

  }
  isXML = (XML_Bool)(isXML != 0 && len == xmlLen);
  isXMLNS = (XML_Bool)(isXMLNS != 0 && len == xmlnsLen);
  if(!(mustBeXML == isXML))
    return (enum XML_Error)(mustBeXML != 0 ? 38 : 40);

  else
    if(!(isXMLNS == 0))
      return /*enum*/XML_ERROR_RESERVED_NAMESPACE_URI;

    else
    {
      if(!(parser->m_namespaceSeparator == 0))
        len = len + 1;

      if(!(parser->m_freeBindingList == ((BINDING *)NULL)))
      {
        b = parser->m_freeBindingList;
        if(!(b->uriAlloc >= len))
        {
          if(len >= 2147483624)
            return /*enum*/XML_ERROR_NO_MEMORY;

          XML_Char *temp;
          void *return_value=parser->m_mem.realloc_fcn((void *)b->uri, sizeof(XML_Char) /*1ul*/  * (unsigned long int)(len + 24));
          temp = (XML_Char *)return_value;
          if(temp == ((XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          b->uri = temp;
          b->uriAlloc = len + 24;
        }

        parser->m_freeBindingList = b->nextTagBinding;
      }

      else
      {
        void *return_value$0=parser->m_mem.malloc_fcn(sizeof(BINDING) /*48ul*/ );
        b = (BINDING *)return_value$0;
        if(b == ((BINDING *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        if(len >= 2147483624)
          return /*enum*/XML_ERROR_NO_MEMORY;

        void *return_value$1=parser->m_mem.malloc_fcn(sizeof(XML_Char) /*1ul*/  * (unsigned long int)(len + 24));
        b->uri = (XML_Char *)return_value$1;
        if(b->uri == ((XML_Char *)NULL))
        {
          parser->m_mem.free_fcn((void *)b);
          return /*enum*/XML_ERROR_NO_MEMORY;
        }

        b->uriAlloc = len + 24;
      }
      b->uriLen = len;
      memcpy((void *)b->uri, (const void *)uri, (unsigned long int)len * sizeof(XML_Char) /*1ul*/ );
      if(!(parser->m_namespaceSeparator == 0))
        b->uri[(signed long int)(len - 1)] = parser->m_namespaceSeparator;

      b->prefix = prefix;
      b->attId = attId;
      b->prevPrefixBinding = prefix->binding;
      __CPROVER_bool tmp_if_expr$1;
      if((signed int)*uri == 0)
        tmp_if_expr$1 = prefix == &parser->m_dtd->defaultPrefix ? 1 : 0;

      else
        tmp_if_expr$1 = 0;
      if(tmp_if_expr$1)
        prefix->binding = ((BINDING *)NULL);

      else
        prefix->binding = b;
      b->nextTagBinding = *bindingsPtr;
      *bindingsPtr = b;
      if(!(attId == ((const ATTRIBUTE_ID *)NULL)))
      {
        if(!(parser->m_startNamespaceDeclHandler == ((XML_StartNamespaceDeclHandler)NULL)))
          parser->m_startNamespaceDeclHandler(parser->m_handlerArg, prefix->name, prefix->binding != ((BINDING *)NULL) ? uri : ((const XML_Char *)NULL));

      }

      return /*enum*/XML_ERROR_NONE;
    }
}

// appendAttributeValue
// file xmlparse.c line 5734
static enum XML_Error appendAttributeValue(XML_Parser parser, const ENCODING *enc, XML_Bool isCdata, const char *ptr, const char *end, STRING_POOL *pool, enum XML_Account account)
{
  DTD * const dtd=parser->m_dtd;
  __CPROVER_bool tmp_if_expr;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  XML_Char *return_value_poolAppend;
  __CPROVER_bool tmp_if_expr$2;
  __CPROVER_bool tmp_if_expr$3;
  XML_Bool return_value_poolGrow$0;
  signed int tmp_if_expr$4;
  XML_Char *tmp_post$0;
  XML_Bool return_value_poolGrow$1;
  XML_Char *tmp_post$1;
  __CPROVER_bool tmp_if_expr$8;
  __CPROVER_bool tmp_if_expr$7;
  __CPROVER_bool tmp_if_expr$9;
  {
    const char *next=ptr;
    signed int tok;
    signed int return_value=enc->literalScanners[0l](enc, ptr, end, &next);
    tok = return_value;
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, ptr, next, 5747, account);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    if(tok == -4)
    {
      return /*enum*/XML_ERROR_NONE;
      if(enc == parser->m_encoding)
        parser->m_eventPtr = next;

      return /*enum*/XML_ERROR_INVALID_TOKEN;
      if(enc == parser->m_encoding)
        parser->m_eventPtr = ptr;

      return /*enum*/XML_ERROR_INVALID_TOKEN;
      XML_Char buf[4l];
      signed int i;
      signed int n;
      signed int return_value$0=enc->charRefNumber(enc, ptr);
      n = return_value$0;
      if(!(n >= 0))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = ptr;

        return /*enum*/XML_ERROR_BAD_CHAR_REF;
      }

      if(isCdata == 0 && n == 0x20)
      {
        if(pool->ptr - pool->start == 0l)
          tmp_if_expr = 1;

        else
          tmp_if_expr = (signed int)pool->ptr[(signed long int)-1] == 0x20 ? 1 : 0;
      }

      n=XmlUtf8Encode(n, (ICHAR *)buf);
      i = 0;
      if(!(i >= n))
      {
        __CPROVER_bool tmp_if_expr$0;
        if(pool->ptr == pool->end)
        {
          return_value_poolGrow=poolGrow(pool);
          tmp_if_expr$0 = !(return_value_poolGrow != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$0 = 0;
        signed int tmp_if_expr$1;
        if(tmp_if_expr$0)
          tmp_if_expr$1 = 0;

        else
        {
          tmp_post = pool->ptr;
          pool->ptr = pool->ptr + 1l;
          *tmp_post = buf[(signed long int)i];
          tmp_if_expr$1 = 1;
        }
        if(tmp_if_expr$1 == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

        i = i + 1;
      }

      return_value_poolAppend=poolAppend(pool, enc, ptr, next);
      if(return_value_poolAppend == ((XML_Char *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      next = ptr + (signed long int)enc->minBytesPerChar;
      if(isCdata == 0)
      {
        if(pool->ptr - pool->start == 0l)
          tmp_if_expr$2 = 1;

        else
          tmp_if_expr$2 = (signed int)pool->ptr[(signed long int)-1] == 0x20 ? 1 : 0;
      }

      if(pool->ptr == pool->end)
      {
        return_value_poolGrow$0=poolGrow(pool);
        tmp_if_expr$3 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
      }

      else
        tmp_if_expr$3 = 0;
      if(tmp_if_expr$3)
        tmp_if_expr$4 = 0;

      else
      {
        tmp_post$0 = pool->ptr;
        pool->ptr = pool->ptr + 1l;
        *tmp_post$0 = ' ';
        tmp_if_expr$4 = 1;
      }
      if(tmp_if_expr$4 == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

      const XML_Char *name;
      ENTITY *entity;
      char checkEntityDecl;
      XML_Char ch;
      signed int return_value$1=enc->predefinedEntityName(enc, ptr + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
      ch = (XML_Char)return_value$1;
      if(!(ch == 0))
      {
        accountingDiffTolerated(parser, tok, (char *)&ch, (char *)&ch + (signed long int)sizeof(XML_Char) /*1l*/ , 5816, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
        __CPROVER_bool tmp_if_expr$5;
        if(pool->ptr == pool->end)
        {
          return_value_poolGrow$1=poolGrow(pool);
          tmp_if_expr$5 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$5 = 0;
        signed int tmp_if_expr$6;
        if(tmp_if_expr$5)
          tmp_if_expr$6 = 0;

        else
        {
          tmp_post$1 = pool->ptr;
          pool->ptr = pool->ptr + 1l;
          *tmp_post$1 = ch;
          tmp_if_expr$6 = 1;
        }
        if(tmp_if_expr$6 == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

      }

      name=poolStoreString(&parser->m_temp2Pool, enc, ptr + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
      if(name == ((const XML_Char *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      NAMED *return_value_lookup=lookup(parser, &dtd->generalEntities, name, 0ul);
      entity = (ENTITY *)return_value_lookup;
      (&parser->m_temp2Pool)->ptr = (&parser->m_temp2Pool)->start;
      if(pool == &dtd->pool)
      {
        if(!(parser->m_prologState.documentEntity == 0))
        {
          if(!(dtd->standalone == 0))
            tmp_if_expr$7 = !(parser->m_openInternalEntities != ((OPEN_INTERNAL_ENTITY *)NULL));

          else
            tmp_if_expr$7 = !(dtd->hasParamEntityRefs != 0);
          tmp_if_expr$8 = tmp_if_expr$7 ? 1 : 0;
        }

        else
          tmp_if_expr$8 = 0;
        checkEntityDecl = (char)tmp_if_expr$8;
      }

      else
      {
        if(dtd->hasParamEntityRefs == 0)
          tmp_if_expr$9 = 1;

        else
          tmp_if_expr$9 = dtd->standalone != 0 ? 1 : 0;
        checkEntityDecl = (char)tmp_if_expr$9;
      }
      if(!(checkEntityDecl == 0))
      {
        if(entity == ((ENTITY *)NULL))
          return /*enum*/XML_ERROR_UNDEFINED_ENTITY;

        else
          if(entity->is_internal == 0)
            return /*enum*/XML_ERROR_ENTITY_DECLARED_IN_PE;

      }

      if(!(entity->open == 0))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = ptr;

        return /*enum*/XML_ERROR_RECURSIVE_ENTITY_REF;
      }

      if(!(entity->notation == ((const XML_Char *)NULL)))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = ptr;

        return /*enum*/XML_ERROR_BINARY_ENTITY_REF;
      }

      if(entity->textPtr == ((const XML_Char *)NULL))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = ptr;

        return /*enum*/XML_ERROR_ATTRIBUTE_EXTERNAL_ENTITY_REF;
      }

      else
      {
        enum XML_Error result;
        const XML_Char *textEnd=entity->textPtr + (signed long int)entity->textLen;
        entity->open = 1;
        entityTrackingOnOpen(parser, entity, 5897);
        result=appendAttributeValue(parser, parser->m_internalEncoding, isCdata, (const char *)entity->textPtr, (const char *)textEnd, pool, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
        entityTrackingOnClose(parser, entity, 5904);
        entity->open = 0;
        if(!(result == /*enum*/XML_ERROR_NONE))
          return result;

      }
    }

    if(enc == parser->m_encoding)
      parser->m_eventPtr = ptr;

    return /*enum*/XML_ERROR_UNEXPECTED_STATE;
    ptr = next;
  }
}

// build_model
// file xmlparse.c line 7335
static XML_Content * build_model(XML_Parser parser)
{
  DTD * const dtd=parser->m_dtd;
  XML_Content *ret;
  XML_Char *str;
  if(!(18446744073709551615ul + -((unsigned long int)dtd->contentStringLen) >= (unsigned long int)dtd->scaffCount * sizeof(XML_Content) /*32ul*/ ))
    return ((XML_Content *)NULL);

  else
  {
    const size_t allocsize=(unsigned long int)dtd->scaffCount * sizeof(XML_Content) /*32ul*/  + (unsigned long int)dtd->contentStringLen * sizeof(XML_Char) /*1ul*/ ;
    void *return_value=parser->m_mem.malloc_fcn(allocsize);
    ret = (XML_Content *)return_value;
    if(ret == ((XML_Content *)NULL))
      return ((XML_Content *)NULL);

    else
    {
      XML_Content *dest=ret;
      XML_Content * const destLimit=&ret[(signed long int)dtd->scaffCount];
      XML_Content * const stackBottom=&ret[(signed long int)dtd->scaffCount];
      XML_Content *stackTop=stackBottom;
      str = (XML_Char *)&ret[(signed long int)dtd->scaffCount];
      stackTop = stackTop - 1l;
      stackTop->numchildren = 0u;
      if(dest < destLimit)
      {
        signed int src_node;
        XML_Content *tmp_post=stackTop;
        stackTop = stackTop + 1l;
        src_node = (signed int)tmp_post->numchildren;
        dest->type = (dtd->scaffold + (signed long int)src_node)->type;
        dest->quant = (dtd->scaffold + (signed long int)src_node)->quant;
        if((signed int)dest->type == 4)
        {
          const XML_Char *src;
          dest->name = str;
          src = (dtd->scaffold + (signed long int)src_node)->name;
          {
            XML_Char *tmp_post$0=str;
            str = str + 1l;
            *tmp_post$0 = *src;
            if(!(*src == 0))
              src = src + 1l;

          }
          dest->numchildren = 0u;
          dest->children = ((XML_Content *)NULL);
        }

        else
        {
          unsigned int i;
          signed int cn;
          dest->name = ((XML_Char *)NULL);
          dest->numchildren = (unsigned int)(dtd->scaffold + (signed long int)src_node)->childcnt;
          dest->children = &dest[1l];
          stackTop = stackTop - (signed long int)dest->numchildren;
          i = 0u;
          cn = (dtd->scaffold + (signed long int)src_node)->firstchild;
          if(!(i >= dest->numchildren))
          {
            (stackTop + (signed long int)i)->numchildren = (unsigned int)cn;
            i = i + 1u;
            cn = (dtd->scaffold + (signed long int)cn)->nextsib;
          }

        }
        dest = dest + 1l;
      }

      return ret;
    }
  }
}

// cdataSectionProcessor
// file xmlparse.c line 3864
static enum XML_Error cdataSectionProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_doCdataSection=doCdataSection(parser, parser->m_encoding, &start, end, endPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), /*enum*/XML_ACCOUNT_DIRECT);
  result = return_value_doCdataSection;
  if(!((signed int)result == 0))
    return result;

  else
  {
    if(!(start == ((const char *)NULL)))
    {
      if(!(parser->m_parentParser == ((XML_Parser)NULL)))
      {
        parser->m_processor = externalEntityContentProcessor;
        enum XML_Error return_value_externalEntityContentProcessor=externalEntityContentProcessor(parser, start, end, endPtr);
        return return_value_externalEntityContentProcessor;
      }

      else
      {
        parser->m_processor = contentProcessor;
        enum XML_Error return_value_contentProcessor=contentProcessor(parser, start, end, endPtr);
        return return_value_contentProcessor;
      }
    }

    return result;
  }
}

// contentProcessor
// file xmlparse.c line 2608
static enum XML_Error contentProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_doContent=doContent(parser, 0, parser->m_encoding, start, end, endPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), /*enum*/XML_ACCOUNT_DIRECT);
  result = return_value_doContent;
  if((signed int)result == 0)
  {
    XML_Bool return_value_storeRawNames=storeRawNames(parser);
    if(return_value_storeRawNames == 0)
      return /*enum*/XML_ERROR_NO_MEMORY;

  }

  return result;
}

// copyEntityTable
// file xmlparse.c line 6793
static signed int copyEntityTable(XML_Parser oldParser, HASH_TABLE *newTable, STRING_POOL *newPool, const HASH_TABLE *oldTable)
{
  HASH_TABLE_ITER iter;
  const XML_Char *cachedOldBase=((const XML_Char *)NULL);
  const XML_Char *cachedNewBase=((const XML_Char *)NULL);
  hashTableIterInit(&iter, oldTable);
  while(1)
  {
    ENTITY *newE;
    const XML_Char *name;
    const ENTITY *oldE;
    NAMED *return_value_hashTableIterNext=hashTableIterNext(&iter);
    oldE = (ENTITY *)return_value_hashTableIterNext;
    if(oldE == ((const ENTITY *)NULL))
      break;

    name=poolCopyString(newPool, oldE->name);
    if(name == ((const XML_Char *)NULL))
      return 0;

    NAMED *return_value_lookup=lookup(oldParser, newTable, name, sizeof(ENTITY) /*64ul*/ );
    newE = (ENTITY *)return_value_lookup;
    if(newE == ((ENTITY *)NULL))
      return 0;

    if(!(oldE->systemId == ((const XML_Char *)NULL)))
    {
      const XML_Char *copyEntityTable$$1$$1$$1$$1$$tem;
      const XML_Char *return_value_poolCopyString=poolCopyString(newPool, oldE->systemId);
      copyEntityTable$$1$$1$$1$$1$$tem = return_value_poolCopyString;
      if(copyEntityTable$$1$$1$$1$$1$$tem == ((const XML_Char *)NULL))
        return 0;

      newE->systemId = copyEntityTable$$1$$1$$1$$1$$tem;
      if(!(oldE->base == ((const XML_Char *)NULL)))
      {
        if(oldE->base == cachedOldBase)
          newE->base = cachedNewBase;

        else
        {
          cachedOldBase = oldE->base;
          copyEntityTable$$1$$1$$1$$1$$tem=poolCopyString(newPool, cachedOldBase);
          if(copyEntityTable$$1$$1$$1$$1$$tem == ((const XML_Char *)NULL))
            return 0;

          const XML_Char *tmp_assign=copyEntityTable$$1$$1$$1$$1$$tem;
          newE->base = tmp_assign;
          cachedNewBase = tmp_assign;
        }
      }

      if(!(oldE->publicId == ((const XML_Char *)NULL)))
      {
        copyEntityTable$$1$$1$$1$$1$$tem=poolCopyString(newPool, oldE->publicId);
        if(copyEntityTable$$1$$1$$1$$1$$tem == ((const XML_Char *)NULL))
          return 0;

        newE->publicId = copyEntityTable$$1$$1$$1$$1$$tem;
      }

    }

    else
    {
      const XML_Char *tem;
      const XML_Char *return_value_poolCopyStringN=poolCopyStringN(newPool, oldE->textPtr, oldE->textLen);
      tem = return_value_poolCopyStringN;
      if(tem == ((const XML_Char *)NULL))
        return 0;

      newE->textPtr = tem;
      newE->textLen = oldE->textLen;
    }
    if(!(oldE->notation == ((const XML_Char *)NULL)))
    {
      const XML_Char *copyEntityTable$$1$$1$$1$$3$$tem;
      const XML_Char *return_value_poolCopyString$0=poolCopyString(newPool, oldE->notation);
      copyEntityTable$$1$$1$$1$$3$$tem = return_value_poolCopyString$0;
      if(copyEntityTable$$1$$1$$1$$3$$tem == ((const XML_Char *)NULL))
        return 0;

      newE->notation = copyEntityTable$$1$$1$$1$$3$$tem;
    }

    newE->is_param = oldE->is_param;
    newE->is_internal = oldE->is_internal;
  }
  return 1;
}

// copyString
// file xmlparse.c line 7470
static XML_Char * copyString(const XML_Char *s, const XML_Memory_Handling_Suite *memsuite)
{
  size_t charsRequired=0ul;
  XML_Char *result;
  for( ; !((signed int)s[(signed long int)charsRequired] == 0); charsRequired = charsRequired + 1ul)
    ;
  charsRequired = charsRequired + 1ul;
  void *return_value=memsuite->malloc_fcn(charsRequired * sizeof(XML_Char) /*1ul*/ );
  result = (XML_Char *)return_value;
  if(result == ((XML_Char *)NULL))
    return ((XML_Char *)NULL);

  else
  {
    memcpy((void *)result, (const void *)s, charsRequired * sizeof(XML_Char) /*1ul*/ );
    return result;
  }
}

// copy_salt_to_sipkey
// file xmlparse.c line 6874
static void copy_salt_to_sipkey(XML_Parser parser, struct sipkey *key)
{
  key->k[0l] = 0ul;
  unsigned long int return_value_get_hash_secret_salt=get_hash_secret_salt(parser);
  key->k[1l] = return_value_get_hash_secret_salt;
}

// defineAttribute
// file xmlparse.c line 6234
static signed int defineAttribute(ELEMENT_TYPE *type, ATTRIBUTE_ID *attId, XML_Bool isCdata, XML_Bool isId, const XML_Char *value, XML_Parser parser)
{
  DEFAULT_ATTRIBUTE *att;
  if(!(value == ((const XML_Char *)NULL)) || !(isId == 0))
  {
    signed int i=0;
    for( ; !(i >= type->nDefaultAtts); i = i + 1)
      if(attId == (type->defaultAtts + (signed long int)i)->id)
        return 1;

    if(!(isId == 0))
    {
      if(type->idAtt == ((const ATTRIBUTE_ID *)NULL))
      {
        if(attId->xmlns == 0)
          type->idAtt = attId;

      }

    }

  }

  if(type->nDefaultAtts == type->allocDefaultAtts)
  {
    if(type->allocDefaultAtts == 0)
    {
      type->allocDefaultAtts = 8;
      void *return_value=parser->m_mem.malloc_fcn((unsigned long int)type->allocDefaultAtts * sizeof(DEFAULT_ATTRIBUTE) /*24ul*/ );
      type->defaultAtts = (DEFAULT_ATTRIBUTE *)return_value;
      if(type->defaultAtts == ((DEFAULT_ATTRIBUTE *)NULL))
      {
        type->allocDefaultAtts = 0;
        return 0;
      }

    }

    else
    {
      DEFAULT_ATTRIBUTE *temp;
      if(type->allocDefaultAtts >= 1073741824)
        return 0;

      signed int count=type->allocDefaultAtts * 2;
      void *return_value$0=parser->m_mem.realloc_fcn((void *)type->defaultAtts, (unsigned long int)count * sizeof(DEFAULT_ATTRIBUTE) /*24ul*/ );
      temp = (DEFAULT_ATTRIBUTE *)return_value$0;
      if(temp == ((DEFAULT_ATTRIBUTE *)NULL))
        return 0;

      type->allocDefaultAtts = count;
      type->defaultAtts = temp;
    }
  }

  att = type->defaultAtts + (signed long int)type->nDefaultAtts;
  att->id = attId;
  att->value = value;
  att->isCdata = isCdata;
  if(isCdata == 0)
    attId->maybeTokenized = 1;

  type->nDefaultAtts = type->nDefaultAtts + 1;
  return 1;
}

// destroyBindings
// file xmlparse.c line 1416
static void destroyBindings(BINDING *bindings, XML_Parser parser)
{
  {
    BINDING *b=bindings;
    if(!(b == ((BINDING *)NULL)))
    {
      bindings = b->nextTagBinding;
      parser->m_mem.free_fcn((void *)b->uri);
      parser->m_mem.free_fcn((void *)b);
    }

  }
}

// doCdataSection
// file xmlparse.c line 3887
static enum XML_Error doCdataSection(XML_Parser parser, const ENCODING *enc, const char **startPtr, const char *end, const char **nextPtr, XML_Bool haveMore, enum XML_Account account)
{
  const char *s=*startPtr;
  const char **eventPP;
  const char **eventEndPP;
  if(enc == parser->m_encoding)
  {
    eventPP = &parser->m_eventPtr;
    *eventPP = s;
    eventEndPP = &parser->m_eventEndPtr;
  }

  else
  {
    eventPP = &parser->m_openInternalEntities->internalEventPtr;
    eventEndPP = &parser->m_openInternalEntities->internalEventEndPtr;
  }
  *eventPP = s;
  *startPtr = ((const char *)NULL);
  __CPROVER_bool tmp_if_expr;
  {
    const char *next=s;
    signed int tok;
    signed int return_value=enc->scanners[2l](enc, s, end, &next);
    tok = return_value;
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 3908, account);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    *eventEndPP = next;
    if(tok == 40)
    {
      if(!(parser->m_endCdataSectionHandler == ((XML_EndCdataSectionHandler)NULL)))
        parser->m_endCdataSectionHandler(parser->m_handlerArg);

      else
      {
        tmp_if_expr = 0;
        if(tmp_if_expr)
          parser->m_characterDataHandler(parser->m_handlerArg, parser->m_dataBuf, 0);

        else
          if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
            reportDefault(parser, enc, s, next);

      }
      *startPtr = next;
      *nextPtr = next;
      if((signed int)parser->m_parsingStatus.parsing == 2)
        return /*enum*/XML_ERROR_ABORTED;

      else
        return /*enum*/XML_ERROR_NONE;
      if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        XML_Char c='\n';
        parser->m_characterDataHandler(parser->m_handlerArg, &c, 1);
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      XML_CharacterDataHandler charDataHandler=parser->m_characterDataHandler;
      if(!(charDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        if(enc->isUtf8 == 0)
        {
          ICHAR *dataPtr=(ICHAR *)parser->m_dataBuf;
          enum XML_Convert_Result convert_res;
          enum XML_Convert_Result return_value$0=enc->utf8Convert(enc, &s, next, &dataPtr, (ICHAR *)parser->m_dataBufEnd);
          convert_res = return_value$0;
          *eventEndPP = next;
          charDataHandler(parser->m_handlerArg, parser->m_dataBuf, (signed int)(dataPtr - (ICHAR *)parser->m_dataBuf));
          if(!((signed int)convert_res == 0) && !((signed int)convert_res == 1))
            *eventPP = s;

        }

        else
          charDataHandler(parser->m_handlerArg, (XML_Char *)s, (signed int)((XML_Char *)next - (XML_Char *)s));
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      *eventPP = next;
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_PARTIAL_CHAR;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_UNCLOSED_CDATA_SECTION;
    }

    *eventPP = next;
    return /*enum*/XML_ERROR_UNEXPECTED_STATE;
    s = next;
    *eventPP = s;
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    if(tmp_switch_value == 3)
    {
      *nextPtr = next;
      return /*enum*/XML_ERROR_NONE;
      return /*enum*/XML_ERROR_ABORTED;
    }

  }
}

// doContent
// file xmlparse.c line 2737
static enum XML_Error doContent(XML_Parser parser, signed int startTagLevel, const ENCODING *enc, const char *s, const char *end, const char **nextPtr, XML_Bool haveMore, enum XML_Account account)
{
  DTD * const dtd=parser->m_dtd;
  const char **eventPP;
  const char **eventEndPP;
  if(enc == parser->m_encoding)
  {
    eventPP = &parser->m_eventPtr;
    eventEndPP = &parser->m_eventEndPtr;
  }

  else
  {
    eventPP = &parser->m_openInternalEntities->internalEventPtr;
    eventEndPP = &parser->m_openInternalEntities->internalEventEndPtr;
  }
  *eventPP = s;
  enum XML_Error return_value_epilogProcessor;
  signed int return_value_memcmp;
  XML_Char *tmp_post;
  const XML_Char *tmp_post$0;
  XML_Char *tmp_post$2;
  const XML_Char *tmp_post$3;
  enum XML_Error return_value_epilogProcessor$0;
  __CPROVER_bool tmp_if_expr$1;
  signed int return_value_reportProcessingInstruction;
  signed int return_value_reportComment;
  {
    const char *next=s;
    signed int tok;
    signed int return_value=enc->scanners[1l](enc, s, end, &next);
    tok = return_value;
    const char *accountAfter=tok == -5 || tok == -3 ? (haveMore != 0 ? s : end) : next;
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, accountAfter, 2762, account);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    *eventEndPP = next;
    if(tok == -3)
    {
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      *eventEndPP = end;
      if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        XML_Char c='\n';
        parser->m_characterDataHandler(parser->m_handlerArg, &c, 1);
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, end);

      if(startTagLevel == 0)
        return /*enum*/XML_ERROR_NO_ELEMENTS;

      if(!(parser->m_tagLevel == startTagLevel))
        return /*enum*/XML_ERROR_ASYNC_ENTITY;

      *nextPtr = end;
      return /*enum*/XML_ERROR_NONE;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      if(startTagLevel >= 1)
      {
        if(!(parser->m_tagLevel == startTagLevel))
          return /*enum*/XML_ERROR_ASYNC_ENTITY;

        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_NO_ELEMENTS;
      *eventPP = next;
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_PARTIAL_CHAR;
      const XML_Char *name;
      ENTITY *entity;
      XML_Char ch;
      signed int return_value$0=enc->predefinedEntityName(enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
      ch = (XML_Char)return_value$0;
      if(!(ch == 0))
      {
        accountingDiffTolerated(parser, tok, (char *)&ch, (char *)&ch + (signed long int)sizeof(XML_Char) /*1l*/ , 2828, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
        if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
          parser->m_characterDataHandler(parser->m_handlerArg, &ch, 1);

        else
          if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
            reportDefault(parser, enc, s, next);

      }

      name=poolStoreString(&dtd->pool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
      if(name == ((const XML_Char *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      NAMED *return_value_lookup=lookup(parser, &dtd->generalEntities, name, 0ul);
      entity = (ENTITY *)return_value_lookup;
      (&dtd->pool)->ptr = (&dtd->pool)->start;
      __CPROVER_bool tmp_if_expr;
      if(dtd->hasParamEntityRefs == 0)
        tmp_if_expr = 1;

      else
        tmp_if_expr = dtd->standalone != 0 ? 1 : 0;
      if(tmp_if_expr)
      {
        if(entity == ((ENTITY *)NULL))
          return /*enum*/XML_ERROR_UNDEFINED_ENTITY;

        else
          if(entity->is_internal == 0)
            return /*enum*/XML_ERROR_ENTITY_DECLARED_IN_PE;

      }

      else
        if(entity == ((ENTITY *)NULL))
        {
          if(!(parser->m_skippedEntityHandler == ((XML_SkippedEntityHandler)NULL)))
            parser->m_skippedEntityHandler(parser->m_handlerArg, name, 0);

          else
            if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
              reportDefault(parser, enc, s, next);

        }

      if(!(entity->open == 0))
        return /*enum*/XML_ERROR_RECURSIVE_ENTITY_REF;

      if(!(entity->notation == ((const XML_Char *)NULL)))
        return /*enum*/XML_ERROR_BINARY_ENTITY_REF;

      if(!(entity->textPtr == ((const XML_Char *)NULL)))
      {
        enum XML_Error doContent$$1$$3$$1$$2$$7$$4$$result;
        if(parser->m_defaultExpandInternalEntities == 0)
        {
          if(!(parser->m_skippedEntityHandler == ((XML_SkippedEntityHandler)NULL)))
            parser->m_skippedEntityHandler(parser->m_handlerArg, entity->name, 0);

          else
            if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
              reportDefault(parser, enc, s, next);

        }

        doContent$$1$$3$$1$$2$$7$$4$$result=processInternalEntity(parser, entity, 0);
        if(!((signed int)doContent$$1$$3$$1$$2$$7$$4$$result == 0))
          return doContent$$1$$3$$1$$2$$7$$4$$result;

      }

      else
        if(!(parser->m_externalEntityRefHandler == ((XML_ExternalEntityRefHandler)NULL)))
        {
          const XML_Char *context;
          entity->open = 1;
          context=getContext(parser);
          entity->open = 0;
          if(context == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          signed int return_value$1=parser->m_externalEntityRefHandler(parser->m_externalEntityRefHandlerArg, context, entity->base, entity->systemId, entity->publicId);
          if(return_value$1 == 0)
            return /*enum*/XML_ERROR_EXTERNAL_ENTITY_HANDLING;

          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->start;
        }

        else
          if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
            reportDefault(parser, enc, s, next);

      TAG *tag;
      enum XML_Error result;
      XML_Char *toPtr;
      if(!(parser->m_freeTagList == ((TAG *)NULL)))
      {
        tag = parser->m_freeTagList;
        parser->m_freeTagList = parser->m_freeTagList->parent;
      }

      else
      {
        void *return_value$2=parser->m_mem.malloc_fcn(sizeof(TAG) /*88ul*/ );
        tag = (TAG *)return_value$2;
        if(tag == ((TAG *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        void *return_value$3=parser->m_mem.malloc_fcn(32ul);
        tag->buf = (char *)return_value$3;
        if(tag->buf == ((char *)NULL))
        {
          parser->m_mem.free_fcn((void *)tag);
          return /*enum*/XML_ERROR_NO_MEMORY;
        }

        tag->bufEnd = tag->buf + 32l;
      }
      tag->bindings = ((BINDING *)NULL);
      tag->parent = parser->m_tagStack;
      parser->m_tagStack = tag;
      tag->name.localPart = ((const XML_Char *)NULL);
      tag->name.prefix = ((const XML_Char *)NULL);
      tag->rawName = s + (signed long int)enc->minBytesPerChar;
      signed int return_value$4=enc->nameLength(enc, tag->rawName);
      tag->rawNameLength = return_value$4;
      parser->m_tagLevel = parser->m_tagLevel + 1;
      const char *rawNameEnd=tag->rawName + (signed long int)tag->rawNameLength;
      const char *fromPtr=tag->rawName;
      toPtr = (XML_Char *)tag->buf;
      {
        signed int bufSize;
        signed int convLen;
        enum XML_Convert_Result doContent$$1$$3$$1$$2$$8$$3$$1$$1$$convert_res;
        enum XML_Convert_Result return_value$5=enc->utf8Convert(enc, &fromPtr, rawNameEnd, (ICHAR **)&toPtr, (ICHAR *)tag->bufEnd - 1l);
        doContent$$1$$3$$1$$2$$8$$3$$1$$1$$convert_res = return_value$5;
        convLen = (signed int)(toPtr - (XML_Char *)tag->buf);
        if(fromPtr >= rawNameEnd || (signed int)doContent$$1$$3$$1$$2$$8$$3$$1$$1$$convert_res == 1)
          tag->name.strLen = convLen;

        else
        {
          bufSize = (signed int)(tag->bufEnd - tag->buf) << 1;
          char *temp;
          void *return_value$6=parser->m_mem.realloc_fcn((void *)tag->buf, (size_t)bufSize);
          temp = (char *)return_value$6;
          if(temp == ((char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          tag->buf = temp;
          tag->bufEnd = temp + (signed long int)bufSize;
          toPtr = (XML_Char *)temp + (signed long int)convLen;
        }
      }
      tag->name.str = (XML_Char *)tag->buf;
      *toPtr = 0;
      result=storeAtts(parser, enc, s, &tag->name, &tag->bindings, account);
      if(!(result == /*enum*/XML_ERROR_NONE))
        return result;

      if(!(parser->m_startElementHandler == ((XML_StartElementHandler)NULL)))
        parser->m_startElementHandler(parser->m_handlerArg, tag->name.str, (const XML_Char **)parser->m_atts);

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      poolClear(&parser->m_tempPool);
      const char *doContent$$1$$3$$1$$2$$9$$rawName=s + (signed long int)enc->minBytesPerChar;
      enum XML_Error doContent$$1$$3$$1$$2$$9$$result;
      BINDING *bindings=((BINDING *)NULL);
      XML_Bool noElmHandlers=1;
      TAG_NAME doContent$$1$$3$$1$$2$$9$$name;
      signed int return_value$7=enc->nameLength(enc, doContent$$1$$3$$1$$2$$9$$rawName);
      doContent$$1$$3$$1$$2$$9$$name.str=poolStoreString(&parser->m_tempPool, enc, doContent$$1$$3$$1$$2$$9$$rawName, doContent$$1$$3$$1$$2$$9$$rawName + (signed long int)return_value$7);
      if(doContent$$1$$3$$1$$2$$9$$name.str == ((const XML_Char *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
      doContent$$1$$3$$1$$2$$9$$result=storeAtts(parser, enc, s, &doContent$$1$$3$$1$$2$$9$$name, &bindings, /*enum*/XML_ACCOUNT_NONE);
      if(!((signed int)doContent$$1$$3$$1$$2$$9$$result == 0))
      {
        freeBindings(parser, bindings);
        return doContent$$1$$3$$1$$2$$9$$result;
      }

      (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
      if(!(parser->m_startElementHandler == ((XML_StartElementHandler)NULL)))
      {
        parser->m_startElementHandler(parser->m_handlerArg, doContent$$1$$3$$1$$2$$9$$name.str, (const XML_Char **)parser->m_atts);
        noElmHandlers = 0;
      }

      if(!(parser->m_endElementHandler == ((XML_EndElementHandler)NULL)))
      {
        if(!(parser->m_startElementHandler == ((XML_StartElementHandler)NULL)))
          *eventPP = *eventEndPP;

        parser->m_endElementHandler(parser->m_handlerArg, doContent$$1$$3$$1$$2$$9$$name.str);
        noElmHandlers = 0;
      }

      if(!(noElmHandlers == 0))
      {
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      }

      poolClear(&parser->m_tempPool);
      freeBindings(parser, bindings);
      if(parser->m_tagLevel == 0)
      {
        if(!((signed int)parser->m_parsingStatus.parsing == 2))
        {
          if((signed int)parser->m_parsingStatus.parsing == 3)
            parser->m_processor = epilogProcessor;

          else
          {
            return_value_epilogProcessor=epilogProcessor(parser, next, end, nextPtr);
            return return_value_epilogProcessor;
          }
        }

      }

      if(parser->m_tagLevel == startTagLevel)
        return /*enum*/XML_ERROR_ASYNC_ENTITY;

      else
      {
        signed int len;
        const char *rawName;
        TAG *doContent$$1$$3$$1$$2$$11$$tag=parser->m_tagStack;
        parser->m_tagStack = doContent$$1$$3$$1$$2$$11$$tag->parent;
        doContent$$1$$3$$1$$2$$11$$tag->parent = parser->m_freeTagList;
        parser->m_freeTagList = doContent$$1$$3$$1$$2$$11$$tag;
        rawName = s + (signed long int)(enc->minBytesPerChar * 2);
        len=enc->nameLength(enc, rawName);
        __CPROVER_bool tmp_if_expr$0;
        if(!(len == doContent$$1$$3$$1$$2$$11$$tag->rawNameLength))
          tmp_if_expr$0 = 1;

        else
        {
          return_value_memcmp=memcmp((const void *)doContent$$1$$3$$1$$2$$11$$tag->rawName, (const void *)rawName, (size_t)len);
          tmp_if_expr$0 = return_value_memcmp != 0 ? 1 : 0;
        }
        if(tmp_if_expr$0)
        {
          *eventPP = rawName;
          return /*enum*/XML_ERROR_TAG_MISMATCH;
        }

        parser->m_tagLevel = parser->m_tagLevel - 1;
        if(!(parser->m_endElementHandler == ((XML_EndElementHandler)NULL)))
        {
          const XML_Char *localPart;
          const XML_Char *prefix;
          XML_Char *uri;
          localPart = doContent$$1$$3$$1$$2$$11$$tag->name.localPart;
          if(!(parser->m_ns == 0))
          {
            if(!(localPart == ((const XML_Char *)NULL)))
            {
              uri = (XML_Char *)doContent$$1$$3$$1$$2$$11$$tag->name.str + (signed long int)doContent$$1$$3$$1$$2$$11$$tag->name.uriLen;
              if(!(*localPart == 0))
              {
                tmp_post = uri;
                uri = uri + 1l;
                tmp_post$0 = localPart;
                localPart = localPart + 1l;
                *tmp_post = *tmp_post$0;
              }

              prefix = (XML_Char *)doContent$$1$$3$$1$$2$$11$$tag->name.prefix;
              if(!(parser->m_ns_triplets == 0))
              {
                if(!(prefix == ((const XML_Char *)NULL)))
                {
                  XML_Char *tmp_post$1=uri;
                  uri = uri + 1l;
                  *tmp_post$1 = parser->m_namespaceSeparator;
                  if(!(*prefix == 0))
                  {
                    tmp_post$2 = uri;
                    uri = uri + 1l;
                    tmp_post$3 = prefix;
                    prefix = prefix + 1l;
                    *tmp_post$2 = *tmp_post$3;
                  }

                }

              }

              *uri = 0;
            }

          }

          parser->m_endElementHandler(parser->m_handlerArg, doContent$$1$$3$$1$$2$$11$$tag->name.str);
        }

        else
          if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
            reportDefault(parser, enc, s, next);

        if(!(doContent$$1$$3$$1$$2$$11$$tag->bindings == ((BINDING *)NULL)))
        {
          BINDING *b=doContent$$1$$3$$1$$2$$11$$tag->bindings;
          if(!(parser->m_endNamespaceDeclHandler == ((XML_EndNamespaceDeclHandler)NULL)))
            parser->m_endNamespaceDeclHandler(parser->m_handlerArg, b->prefix->name);

          doContent$$1$$3$$1$$2$$11$$tag->bindings = doContent$$1$$3$$1$$2$$11$$tag->bindings->nextTagBinding;
          b->nextTagBinding = parser->m_freeBindingList;
          parser->m_freeBindingList = b;
          b->prefix->binding = b->prevPrefixBinding;
        }

        if(parser->m_tagLevel == 0)
        {
          if(!((signed int)parser->m_parsingStatus.parsing == 2))
          {
            if((signed int)parser->m_parsingStatus.parsing == 3)
              parser->m_processor = epilogProcessor;

            else
            {
              return_value_epilogProcessor$0=epilogProcessor(parser, next, end, nextPtr);
              return return_value_epilogProcessor$0;
            }
          }

        }

      }
      signed int n;
      signed int return_value$8=enc->charRefNumber(enc, s);
      n = return_value$8;
      if(!(n >= 0))
        return /*enum*/XML_ERROR_BAD_CHAR_REF;

      if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        XML_Char buf[4l];
        signed int return_value_XmlUtf8Encode=XmlUtf8Encode(n, (ICHAR *)buf);
        parser->m_characterDataHandler(parser->m_handlerArg, buf, return_value_XmlUtf8Encode);
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      return /*enum*/XML_ERROR_MISPLACED_XML_PI;
      if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        XML_Char doContent$$1$$3$$1$$2$$13$$c='\n';
        parser->m_characterDataHandler(parser->m_handlerArg, &doContent$$1$$3$$1$$2$$13$$c, 1);
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      enum XML_Error doContent$$1$$3$$1$$2$$14$$result;
      if(!(parser->m_startCdataSectionHandler == ((XML_StartCdataSectionHandler)NULL)))
        parser->m_startCdataSectionHandler(parser->m_handlerArg);

      else
      {
        tmp_if_expr$1 = 0;
        if(tmp_if_expr$1)
          parser->m_characterDataHandler(parser->m_handlerArg, parser->m_dataBuf, 0);

        else
          if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
            reportDefault(parser, enc, s, next);

      }
      doContent$$1$$3$$1$$2$$14$$result=doCdataSection(parser, enc, &next, end, nextPtr, haveMore, account);
      if(!((signed int)doContent$$1$$3$$1$$2$$14$$result == 0))
        return doContent$$1$$3$$1$$2$$14$$result;

      else
        if(next == ((const char *)NULL))
        {
          parser->m_processor = cdataSectionProcessor;
          return doContent$$1$$3$$1$$2$$14$$result;
        }

      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      if(!(parser->m_characterDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        if(enc->isUtf8 == 0)
        {
          ICHAR *dataPtr=(ICHAR *)parser->m_dataBuf;
          enc->utf8Convert(enc, &s, end, &dataPtr, (ICHAR *)parser->m_dataBufEnd);
          parser->m_characterDataHandler(parser->m_handlerArg, parser->m_dataBuf, (signed int)(dataPtr - (ICHAR *)parser->m_dataBuf));
        }

        else
          parser->m_characterDataHandler(parser->m_handlerArg, (XML_Char *)s, (signed int)((XML_Char *)end - (XML_Char *)s));
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, end);

      if(startTagLevel == 0)
      {
        *eventPP = end;
        return /*enum*/XML_ERROR_NO_ELEMENTS;
      }

      if(!(parser->m_tagLevel == startTagLevel))
      {
        *eventPP = end;
        return /*enum*/XML_ERROR_ASYNC_ENTITY;
      }

      *nextPtr = end;
      return /*enum*/XML_ERROR_NONE;
      XML_CharacterDataHandler charDataHandler=parser->m_characterDataHandler;
      if(!(charDataHandler == ((XML_CharacterDataHandler)NULL)))
      {
        if(enc->isUtf8 == 0)
        {
          ICHAR *doContent$$1$$3$$1$$2$$19$$1$$1$$1$$1$$dataPtr=(ICHAR *)parser->m_dataBuf;
          enum XML_Convert_Result convert_res;
          enum XML_Convert_Result return_value$9=enc->utf8Convert(enc, &s, next, &doContent$$1$$3$$1$$2$$19$$1$$1$$1$$1$$dataPtr, (ICHAR *)parser->m_dataBufEnd);
          convert_res = return_value$9;
          *eventEndPP = s;
          charDataHandler(parser->m_handlerArg, parser->m_dataBuf, (signed int)(doContent$$1$$3$$1$$2$$19$$1$$1$$1$$1$$dataPtr - (ICHAR *)parser->m_dataBuf));
          if(!((signed int)convert_res == 0) && !((signed int)convert_res == 1))
            *eventPP = s;

        }

        else
          charDataHandler(parser->m_handlerArg, (XML_Char *)s, (signed int)((XML_Char *)next - (XML_Char *)s));
      }

      else
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

      return_value_reportProcessingInstruction=reportProcessingInstruction(parser, enc, s, next);
      if(return_value_reportProcessingInstruction == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

      return_value_reportComment=reportComment(parser, enc, s, next);
      if(return_value_reportComment == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

    }

    if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
      reportDefault(parser, enc, s, next);

    s = next;
    *eventPP = s;
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    if(tmp_switch_value == 3)
    {
      *nextPtr = next;
      return /*enum*/XML_ERROR_NONE;
      return /*enum*/XML_ERROR_ABORTED;
    }

  }
}

// doIgnoreSection
// file xmlparse.c line 4029
static enum XML_Error doIgnoreSection(XML_Parser parser, const ENCODING *enc, const char **startPtr, const char *end, const char **nextPtr, XML_Bool haveMore)
{
  const char *next=*startPtr;
  signed int tok;
  const char *s=*startPtr;
  const char **eventPP;
  const char **eventEndPP;
  if(enc == parser->m_encoding)
  {
    eventPP = &parser->m_eventPtr;
    *eventPP = s;
    eventEndPP = &parser->m_eventEndPtr;
  }

  else
  {
    eventPP = &parser->m_openInternalEntities->internalEventPtr;
    eventEndPP = &parser->m_openInternalEntities->internalEventEndPtr;
  }
  *eventPP = s;
  *startPtr = ((const char *)NULL);
  tok=enc->scanners[3l](enc, s, end, &next);
  XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 4060, /*enum*/XML_ACCOUNT_DIRECT);
  if(return_value_accountingDiffTolerated == 0)
  {
    accountingOnAbort(parser);
    return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
  }

  else
  {
    *eventEndPP = next;
    if(tok == 42)
    {
      if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
        reportDefault(parser, enc, s, next);

      *startPtr = next;
      *nextPtr = next;
      if((signed int)parser->m_parsingStatus.parsing == 2)
        return /*enum*/XML_ERROR_ABORTED;

      else
        return /*enum*/XML_ERROR_NONE;
      *eventPP = next;
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_PARTIAL_CHAR;
      if(!(haveMore == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_SYNTAX;
    }

    *eventPP = next;
    return /*enum*/XML_ERROR_UNEXPECTED_STATE;
  }
}

// doProlog
// file xmlparse.c line 4477
static enum XML_Error doProlog(XML_Parser parser, const ENCODING *enc, const char *s, const char *end, signed int tok, const char *next, const char **nextPtr, XML_Bool haveMore, XML_Bool allowClosingDoctype, enum XML_Account account)
{
  DTD * const dtd=parser->m_dtd;
  const char **eventPP;
  const char **eventEndPP;
  enum XML_Content_Quant quant;
  if(enc == parser->m_encoding)
  {
    eventPP = &parser->m_eventPtr;
    eventEndPP = &parser->m_eventEndPtr;
  }

  else
  {
    eventPP = &parser->m_openInternalEntities->internalEventPtr;
    eventEndPP = &parser->m_openInternalEntities->internalEventEndPtr;
  }
  __CPROVER_bool tmp_if_expr;
  signed int return_value$3;
  signed int return_value$5;
  __CPROVER_bool tmp_if_expr$7;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  __CPROVER_bool tmp_if_expr$4;
  XML_Bool return_value_poolGrow$0;
  signed int tmp_if_expr$5;
  XML_Char *tmp_post$0;
  __CPROVER_bool tmp_if_expr$14;
  XML_Bool return_value_poolGrow$1;
  XML_Char *tmp_post$1;
  __CPROVER_bool tmp_if_expr$11;
  XML_Bool return_value_poolGrow$2;
  signed int tmp_if_expr$12;
  XML_Char *tmp_post$2;
  signed int return_value$6;
  __CPROVER_bool tmp_if_expr$18;
  signed int return_value$13;
  {
    signed int role;
    XML_Bool handleDefault=1;
    *eventPP = s;
    *eventEndPP = next;
    if(!(tok >= 1))
    {
      if(!(haveMore == 0) && !(tok == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      switch(tok)
      {
        case 0:
        {
          *eventPP = next;
          return /*enum*/XML_ERROR_INVALID_TOKEN;
        }
        case -1:
          return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
        case -2:
          return /*enum*/XML_ERROR_PARTIAL_CHAR;
        case -15:
        {
          tok = -tok;
          break;
        }
        case -4:
        {
          if(!(enc == parser->m_encoding))
          {
            if(parser->m_openInternalEntities->betweenDecl == 0)
            {
              *nextPtr = s;
              return /*enum*/XML_ERROR_NONE;
            }

          }

          if(!(parser->m_isParamEntity == 0))
            tmp_if_expr = 1;

          else
            tmp_if_expr = enc != parser->m_encoding ? 1 : 0;
          if(tmp_if_expr)
          {
            signed int return_value=(&parser->m_prologState)->handler(&parser->m_prologState, -4, end, end, enc);
            if(return_value == -1)
              return /*enum*/XML_ERROR_INCOMPLETE_PE;

            *nextPtr = s;
            return /*enum*/XML_ERROR_NONE;
          }

          return /*enum*/XML_ERROR_NO_ELEMENTS;
        }
        default:
        {
          tok = -tok;
          next = end;
        }
      }
    }

    role=(&parser->m_prologState)->handler(&parser->m_prologState, tok, s, next, enc);
    if(!(role == 57) && !(role == 1) && !(role == 2))
    {
      XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 4581, account);
      if(return_value_accountingDiffTolerated == 0)
      {
        accountingOnAbort(parser);
        return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
      }

    }

    if(role == 1)
    {
      enum XML_Error doProlog$$1$$3$$1$$3$$1$$result;
      enum XML_Error return_value_processXmlDecl=processXmlDecl(parser, 0, s, next);
      doProlog$$1$$3$$1$$3$$1$$result = return_value_processXmlDecl;
      if(!((signed int)doProlog$$1$$3$$1$$3$$1$$result == 0))
        return doProlog$$1$$3$$1$$3$$1$$result;

      enc = parser->m_encoding;
      handleDefault = 0;
      if(!(parser->m_startDoctypeDeclHandler == ((XML_StartDoctypeDeclHandler)NULL)))
      {
        XML_Char *return_value_poolStoreString=poolStoreString(&parser->m_tempPool, enc, s, next);
        parser->m_doctypeName = return_value_poolStoreString;
        if(parser->m_doctypeName == ((const XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
        parser->m_doctypePubid = ((const XML_Char *)NULL);
        handleDefault = 0;
      }

      parser->m_doctypeSysid = ((const XML_Char *)NULL);
      if(!(parser->m_startDoctypeDeclHandler == ((XML_StartDoctypeDeclHandler)NULL)))
      {
        parser->m_startDoctypeDeclHandler(parser->m_handlerArg, parser->m_doctypeName, parser->m_doctypeSysid, parser->m_doctypePubid, 1);
        parser->m_doctypeName = ((const XML_Char *)NULL);
        poolClear(&parser->m_tempPool);
        handleDefault = 0;
      }

      enum XML_Error result;
      enum XML_Error return_value_processXmlDecl$0=processXmlDecl(parser, 1, s, next);
      result = return_value_processXmlDecl$0;
      if(!((signed int)result == 0))
        return result;

      enc = parser->m_encoding;
      handleDefault = 0;
      parser->m_useForeignDTD = 0;
      static const XML_Char externalSubsetName[2l]={ '#', 0 };
      NAMED *return_value_lookup=lookup(parser, &dtd->paramEntities, externalSubsetName, sizeof(ENTITY) /*64ul*/ );
      parser->m_declEntity = (ENTITY *)return_value_lookup;
      if(parser->m_declEntity == ((ENTITY *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      dtd->hasParamEntityRefs = 1;
      if(!(parser->m_startDoctypeDeclHandler == ((XML_StartDoctypeDeclHandler)NULL)))
      {
        XML_Char *pubId;
        signed int return_value$0=enc->isPublicId(enc, s, next, eventPP);
        if(return_value$0 == 0)
          return /*enum*/XML_ERROR_PUBLICID;

        pubId=poolStoreString(&parser->m_tempPool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
        if(pubId == ((XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        normalizePublicId(pubId);
        (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
        parser->m_doctypePubid = pubId;
        handleDefault = 0;
      }

      signed int return_value$1=enc->isPublicId(enc, s, next, eventPP);
      if(return_value$1 == 0)
        return /*enum*/XML_ERROR_PUBLICID;


    alreadyChecked:
      ;
      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_declEntity == ((ENTITY *)NULL)))
        {
          XML_Char *tem;
          XML_Char *return_value_poolStoreString$0=poolStoreString(&dtd->pool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
          tem = return_value_poolStoreString$0;
          if(tem == ((XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          normalizePublicId(tem);
          parser->m_declEntity->publicId = tem;
          (&dtd->pool)->start = (&dtd->pool)->ptr;
          if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
          {
            if(role == 14)
              handleDefault = 0;

          }

        }

      }

      if(!(allowClosingDoctype == 1))
        return /*enum*/XML_ERROR_INVALID_TOKEN;

      if(!(parser->m_doctypeName == ((const XML_Char *)NULL)))
      {
        parser->m_startDoctypeDeclHandler(parser->m_handlerArg, parser->m_doctypeName, parser->m_doctypeSysid, parser->m_doctypePubid, 0);
        poolClear(&parser->m_tempPool);
        handleDefault = 0;
      }

      __CPROVER_bool tmp_if_expr$0;
      if(!(parser->m_doctypeSysid == ((const XML_Char *)NULL)))
        tmp_if_expr$0 = 1;

      else
        tmp_if_expr$0 = parser->m_useForeignDTD != 0 ? 1 : 0;
      if(tmp_if_expr$0)
      {
        XML_Bool hadParamEntityRefs=dtd->hasParamEntityRefs;
        dtd->hasParamEntityRefs = 1;
        if(!(parser->m_paramEntityParsing == /*enum*/XML_PARAM_ENTITY_PARSING_NEVER))
        {
          if(!(parser->m_externalEntityRefHandler == ((XML_ExternalEntityRefHandler)NULL)))
          {
            ENTITY *entity;
            NAMED *return_value_lookup$0=lookup(parser, &dtd->paramEntities, externalSubsetName, sizeof(ENTITY) /*64ul*/ );
            entity = (ENTITY *)return_value_lookup$0;
            if(entity == ((ENTITY *)NULL))
              return /*enum*/XML_ERROR_NO_MEMORY;

            if(!(parser->m_useForeignDTD == 0))
              entity->base = parser->m_curBase;

            dtd->paramEntityRead = 0;
            signed int return_value$2=parser->m_externalEntityRefHandler(parser->m_externalEntityRefHandlerArg, ((const XML_Char *)NULL), entity->base, entity->systemId, entity->publicId);
            if(return_value$2 == 0)
              return /*enum*/XML_ERROR_EXTERNAL_ENTITY_HANDLING;

            if(!(dtd->paramEntityRead == 0))
            {
              if(dtd->standalone == 0)
              {
                if(!(parser->m_notStandaloneHandler == ((XML_NotStandaloneHandler)NULL)))
                {
                  return_value$3=parser->m_notStandaloneHandler(parser->m_handlerArg);
                  if(return_value$3 == 0)
                    return /*enum*/XML_ERROR_NOT_STANDALONE;

                }

              }

            }

            else
              if(parser->m_doctypeSysid == ((const XML_Char *)NULL))
                dtd->hasParamEntityRefs = hadParamEntityRefs;

          }

        }

        parser->m_useForeignDTD = 0;
      }

      if(!(parser->m_endDoctypeDeclHandler == ((XML_EndDoctypeDeclHandler)NULL)))
      {
        parser->m_endDoctypeDeclHandler(parser->m_handlerArg);
        handleDefault = 0;
      }

      if(!(parser->m_useForeignDTD == 0))
      {
        XML_Bool doProlog$$1$$3$$1$$3$$11$$hadParamEntityRefs=dtd->hasParamEntityRefs;
        dtd->hasParamEntityRefs = 1;
        if(!(parser->m_paramEntityParsing == /*enum*/XML_PARAM_ENTITY_PARSING_NEVER))
        {
          if(!(parser->m_externalEntityRefHandler == ((XML_ExternalEntityRefHandler)NULL)))
          {
            ENTITY *doProlog$$1$$3$$1$$3$$11$$1$$entity;
            NAMED *return_value_lookup$1=lookup(parser, &dtd->paramEntities, externalSubsetName, sizeof(ENTITY) /*64ul*/ );
            doProlog$$1$$3$$1$$3$$11$$1$$entity = (ENTITY *)return_value_lookup$1;
            if(doProlog$$1$$3$$1$$3$$11$$1$$entity == ((ENTITY *)NULL))
              return /*enum*/XML_ERROR_NO_MEMORY;

            doProlog$$1$$3$$1$$3$$11$$1$$entity->base = parser->m_curBase;
            dtd->paramEntityRead = 0;
            signed int return_value$4=parser->m_externalEntityRefHandler(parser->m_externalEntityRefHandlerArg, ((const XML_Char *)NULL), doProlog$$1$$3$$1$$3$$11$$1$$entity->base, doProlog$$1$$3$$1$$3$$11$$1$$entity->systemId, doProlog$$1$$3$$1$$3$$11$$1$$entity->publicId);
            if(return_value$4 == 0)
              return /*enum*/XML_ERROR_EXTERNAL_ENTITY_HANDLING;

            if(!(dtd->paramEntityRead == 0))
            {
              if(dtd->standalone == 0)
              {
                if(!(parser->m_notStandaloneHandler == ((XML_NotStandaloneHandler)NULL)))
                {
                  return_value$5=parser->m_notStandaloneHandler(parser->m_handlerArg);
                  if(return_value$5 == 0)
                    return /*enum*/XML_ERROR_NOT_STANDALONE;

                }

              }

            }

            else
              dtd->hasParamEntityRefs = doProlog$$1$$3$$1$$3$$11$$hadParamEntityRefs;
          }

        }

      }

      parser->m_processor = contentProcessor;
      enum XML_Error return_value_contentProcessor=contentProcessor(parser, s, end, nextPtr);
      return return_value_contentProcessor;
      ELEMENT_TYPE *return_value_getElementType=getElementType(parser, enc, s, next);
      parser->m_declElementType = return_value_getElementType;
      if(parser->m_declElementType == ((ELEMENT_TYPE *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      ATTRIBUTE_ID *return_value_getAttributeId=getAttributeId(parser, enc, s, next);
      parser->m_declAttributeId = return_value_getAttributeId;
      if(parser->m_declAttributeId == ((ATTRIBUTE_ID *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      parser->m_declAttributeIsCdata = 0;
      parser->m_declAttributeType = ((const XML_Char *)NULL);
      parser->m_declAttributeIsId = 0;
      parser->m_declAttributeIsCdata = 1;
      static const XML_Char atypeCDATA[6l]={ 'C', 'D', 'A', 'T', 'A', 0 };
      parser->m_declAttributeType = atypeCDATA;
      parser->m_declAttributeIsId = 1;
      static const XML_Char atypeID[3l]={ 'I', 'D', 0 };
      parser->m_declAttributeType = atypeID;
      static const XML_Char atypeIDREF[6l]={ 'I', 'D', 'R', 'E', 'F', 0 };
      parser->m_declAttributeType = atypeIDREF;
      static const XML_Char atypeIDREFS[7l]={ 'I', 'D', 'R', 'E', 'F', 'S', 0 };
      parser->m_declAttributeType = atypeIDREFS;
      static const XML_Char atypeENTITY[7l]={ 'E', 'N', 'T', 'I', 'T', 'Y', 0 };
      parser->m_declAttributeType = atypeENTITY;
      static const XML_Char atypeENTITIES[9l]={ 'E', 'N', 'T', 'I', 'T', 'I', 'E', 'S', 0 };
      parser->m_declAttributeType = atypeENTITIES;
      static const XML_Char atypeNMTOKEN[8l]={ 'N', 'M', 'T', 'O', 'K', 'E', 'N', 0 };
      parser->m_declAttributeType = atypeNMTOKEN;
      static const XML_Char atypeNMTOKENS[9l]={ 'N', 'M', 'T', 'O', 'K', 'E', 'N', 'S', 0 };
      parser->m_declAttributeType = atypeNMTOKENS;

    checkAttListDeclHandler:
      ;
      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_attlistDeclHandler == ((XML_AttlistDeclHandler)NULL)))
          handleDefault = 0;

      }

      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_attlistDeclHandler == ((XML_AttlistDeclHandler)NULL)))
        {
          const XML_Char *prefix;
          static const XML_Char enumValueSep[2l]={ '|', 0 };
          if(!(parser->m_declAttributeType == ((const XML_Char *)NULL)))
            prefix = enumValueSep;

          else
          {
            const XML_Char *tmp_if_expr$1;
            static const XML_Char enumValueStart[2l]={ '(', 0 };
            static const XML_Char notationPrefix[10l]={ 'N', 'O', 'T', 'A', 'T', 'I', 'O', 'N', '(', 0 };
            if(role == 32)
              tmp_if_expr$1 = notationPrefix;

            else
              tmp_if_expr$1 = enumValueStart;
            prefix = tmp_if_expr$1;
          }
          const XML_Char *return_value_poolAppendString=poolAppendString(&parser->m_tempPool, prefix);
          if(return_value_poolAppendString == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          XML_Char *return_value_poolAppend=poolAppend(&parser->m_tempPool, enc, s, next);
          if(return_value_poolAppend == ((XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          parser->m_declAttributeType = parser->m_tempPool.start;
          handleDefault = 0;
        }

      }

      if(!(dtd->keepProcessing == 0))
      {
        signed int return_value_defineAttribute=defineAttribute(parser->m_declElementType, parser->m_declAttributeId, parser->m_declAttributeIsCdata, parser->m_declAttributeIsId, ((const XML_Char *)NULL), parser);
        if(return_value_defineAttribute == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

        if(!(parser->m_attlistDeclHandler == ((XML_AttlistDeclHandler)NULL)))
        {
          if(!(parser->m_declAttributeType == ((const XML_Char *)NULL)))
          {
            __CPROVER_bool tmp_if_expr$8;
            if((signed int)*parser->m_declAttributeType == 0x28)
              tmp_if_expr$8 = 1;

            else
            {
              if((signed int)*parser->m_declAttributeType == 0x4E)
                tmp_if_expr$7 = (signed int)parser->m_declAttributeType[1l] == 0x4F ? 1 : 0;

              else
                tmp_if_expr$7 = 0;
              tmp_if_expr$8 = tmp_if_expr$7 ? 1 : 0;
            }
            if(tmp_if_expr$8)
            {
              __CPROVER_bool tmp_if_expr$2;
              if(parser->m_tempPool.ptr == parser->m_tempPool.end)
              {
                return_value_poolGrow=poolGrow(&parser->m_tempPool);
                tmp_if_expr$2 = !(return_value_poolGrow != 0) ? 1 : 0;
              }

              else
                tmp_if_expr$2 = 0;
              signed int tmp_if_expr$3;
              if(tmp_if_expr$2)
                tmp_if_expr$3 = 0;

              else
              {
                tmp_post = (&parser->m_tempPool)->ptr;
                (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
                *tmp_post = ')';
                tmp_if_expr$3 = 1;
              }
              __CPROVER_bool tmp_if_expr$6;
              if(tmp_if_expr$3 == 0)
                tmp_if_expr$6 = 1;

              else
              {
                if(parser->m_tempPool.ptr == parser->m_tempPool.end)
                {
                  return_value_poolGrow$0=poolGrow(&parser->m_tempPool);
                  tmp_if_expr$4 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
                }

                else
                  tmp_if_expr$4 = 0;
                if(tmp_if_expr$4)
                  tmp_if_expr$5 = 0;

                else
                {
                  tmp_post$0 = (&parser->m_tempPool)->ptr;
                  (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
                  *tmp_post$0 = 0;
                  tmp_if_expr$5 = 1;
                }
                tmp_if_expr$6 = !(tmp_if_expr$5 != 0) ? 1 : 0;
              }
              if(tmp_if_expr$6)
                return /*enum*/XML_ERROR_NO_MEMORY;

              parser->m_declAttributeType = parser->m_tempPool.start;
              (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
            }

            *eventEndPP = s;
            parser->m_attlistDeclHandler(parser->m_handlerArg, parser->m_declElementType->name, parser->m_declAttributeId->name, parser->m_declAttributeType, ((const XML_Char *)NULL), (signed int)(role == 36));
            poolClear(&parser->m_tempPool);
            handleDefault = 0;
          }

        }

      }

      if(!(dtd->keepProcessing == 0))
      {
        const XML_Char *attVal;
        enum XML_Error doProlog$$1$$3$$1$$3$$14$$result;
        enum XML_Error return_value_storeAttributeValue=storeAttributeValue(parser, enc, parser->m_declAttributeIsCdata, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar, &dtd->pool, /*enum*/XML_ACCOUNT_NONE);
        doProlog$$1$$3$$1$$3$$14$$result = return_value_storeAttributeValue;
        if(!(doProlog$$1$$3$$1$$3$$14$$result == /*enum*/XML_ERROR_NONE))
          return doProlog$$1$$3$$1$$3$$14$$result;

        attVal = (&dtd->pool)->start;
        (&dtd->pool)->start = (&dtd->pool)->ptr;
        signed int return_value_defineAttribute$0=defineAttribute(parser->m_declElementType, parser->m_declAttributeId, parser->m_declAttributeIsCdata, 0, attVal, parser);
        if(return_value_defineAttribute$0 == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

        if(!(parser->m_attlistDeclHandler == ((XML_AttlistDeclHandler)NULL)))
        {
          if(!(parser->m_declAttributeType == ((const XML_Char *)NULL)))
          {
            __CPROVER_bool tmp_if_expr$15;
            if((signed int)*parser->m_declAttributeType == 0x28)
              tmp_if_expr$15 = 1;

            else
            {
              if((signed int)*parser->m_declAttributeType == 0x4E)
                tmp_if_expr$14 = (signed int)parser->m_declAttributeType[1l] == 0x4F ? 1 : 0;

              else
                tmp_if_expr$14 = 0;
              tmp_if_expr$15 = tmp_if_expr$14 ? 1 : 0;
            }
            if(tmp_if_expr$15)
            {
              __CPROVER_bool tmp_if_expr$9;
              if(parser->m_tempPool.ptr == parser->m_tempPool.end)
              {
                return_value_poolGrow$1=poolGrow(&parser->m_tempPool);
                tmp_if_expr$9 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
              }

              else
                tmp_if_expr$9 = 0;
              signed int tmp_if_expr$10;
              if(tmp_if_expr$9)
                tmp_if_expr$10 = 0;

              else
              {
                tmp_post$1 = (&parser->m_tempPool)->ptr;
                (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
                *tmp_post$1 = ')';
                tmp_if_expr$10 = 1;
              }
              __CPROVER_bool tmp_if_expr$13;
              if(tmp_if_expr$10 == 0)
                tmp_if_expr$13 = 1;

              else
              {
                if(parser->m_tempPool.ptr == parser->m_tempPool.end)
                {
                  return_value_poolGrow$2=poolGrow(&parser->m_tempPool);
                  tmp_if_expr$11 = !(return_value_poolGrow$2 != 0) ? 1 : 0;
                }

                else
                  tmp_if_expr$11 = 0;
                if(tmp_if_expr$11)
                  tmp_if_expr$12 = 0;

                else
                {
                  tmp_post$2 = (&parser->m_tempPool)->ptr;
                  (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
                  *tmp_post$2 = 0;
                  tmp_if_expr$12 = 1;
                }
                tmp_if_expr$13 = !(tmp_if_expr$12 != 0) ? 1 : 0;
              }
              if(tmp_if_expr$13)
                return /*enum*/XML_ERROR_NO_MEMORY;

              parser->m_declAttributeType = parser->m_tempPool.start;
              (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
            }

            *eventEndPP = s;
            parser->m_attlistDeclHandler(parser->m_handlerArg, parser->m_declElementType->name, parser->m_declAttributeId->name, parser->m_declAttributeType, attVal, (signed int)(role == 38));
            poolClear(&parser->m_tempPool);
            handleDefault = 0;
          }

        }

      }

      if(!(dtd->keepProcessing == 0))
      {
        enum XML_Error doProlog$$1$$3$$1$$3$$15$$result;
        enum XML_Error return_value_storeEntityValue=storeEntityValue(parser, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar, /*enum*/XML_ACCOUNT_NONE);
        doProlog$$1$$3$$1$$3$$15$$result = return_value_storeEntityValue;
        if(!(parser->m_declEntity == ((ENTITY *)NULL)))
        {
          parser->m_declEntity->textPtr = (&dtd->entityValuePool)->start;
          parser->m_declEntity->textLen = (signed int)((&dtd->entityValuePool)->ptr - (&dtd->entityValuePool)->start);
          (&dtd->entityValuePool)->start = (&dtd->entityValuePool)->ptr;
          if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
          {
            *eventEndPP = s;
            parser->m_entityDeclHandler(parser->m_handlerArg, parser->m_declEntity->name, (signed int)parser->m_declEntity->is_param, parser->m_declEntity->textPtr, parser->m_declEntity->textLen, parser->m_curBase, ((const XML_Char *)NULL), ((const XML_Char *)NULL), ((const XML_Char *)NULL));
            handleDefault = 0;
          }

        }

        else
          (&dtd->entityValuePool)->ptr = (&dtd->entityValuePool)->start;
        if(!((signed int)doProlog$$1$$3$$1$$3$$15$$result == 0))
          return doProlog$$1$$3$$1$$3$$15$$result;

      }

      parser->m_useForeignDTD = 0;
      dtd->hasParamEntityRefs = 1;
      if(!(parser->m_startDoctypeDeclHandler == ((XML_StartDoctypeDeclHandler)NULL)))
      {
        XML_Char *return_value_poolStoreString$1=poolStoreString(&parser->m_tempPool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
        parser->m_doctypeSysid = return_value_poolStoreString$1;
        if(parser->m_doctypeSysid == ((const XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
        handleDefault = 0;
      }

      else
        parser->m_doctypeSysid = externalSubsetName;
      if(dtd->standalone == 0)
      {
        if(parser->m_paramEntityParsing == /*enum*/XML_PARAM_ENTITY_PARSING_NEVER)
        {
          if(!(parser->m_notStandaloneHandler == ((XML_NotStandaloneHandler)NULL)))
          {
            return_value$6=parser->m_notStandaloneHandler(parser->m_handlerArg);
            if(return_value$6 == 0)
              return /*enum*/XML_ERROR_NOT_STANDALONE;

          }

        }

      }

      if(parser->m_declEntity == ((ENTITY *)NULL))
      {
        NAMED *return_value_lookup$2=lookup(parser, &dtd->paramEntities, externalSubsetName, sizeof(ENTITY) /*64ul*/ );
        parser->m_declEntity = (ENTITY *)return_value_lookup$2;
        if(parser->m_declEntity == ((ENTITY *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        parser->m_declEntity->publicId = ((const XML_Char *)NULL);
      }

      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_declEntity == ((ENTITY *)NULL)))
        {
          XML_Char *return_value_poolStoreString$2=poolStoreString(&dtd->pool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
          parser->m_declEntity->systemId = return_value_poolStoreString$2;
          if(parser->m_declEntity->systemId == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          parser->m_declEntity->base = parser->m_curBase;
          (&dtd->pool)->start = (&dtd->pool)->ptr;
          if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
          {
            if(role == 13)
              handleDefault = 0;

          }

        }

      }

      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_declEntity == ((ENTITY *)NULL)))
        {
          if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
          {
            *eventEndPP = s;
            parser->m_entityDeclHandler(parser->m_handlerArg, parser->m_declEntity->name, (signed int)parser->m_declEntity->is_param, ((const XML_Char *)NULL), 0, parser->m_declEntity->base, parser->m_declEntity->systemId, parser->m_declEntity->publicId, ((const XML_Char *)NULL));
            handleDefault = 0;
          }

        }

      }

      if(!(dtd->keepProcessing == 0))
      {
        if(!(parser->m_declEntity == ((ENTITY *)NULL)))
        {
          XML_Char *return_value_poolStoreString$3=poolStoreString(&dtd->pool, enc, s, next);
          parser->m_declEntity->notation = return_value_poolStoreString$3;
          if(parser->m_declEntity->notation == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          (&dtd->pool)->start = (&dtd->pool)->ptr;
          if(!(parser->m_unparsedEntityDeclHandler == ((XML_UnparsedEntityDeclHandler)NULL)))
          {
            *eventEndPP = s;
            parser->m_unparsedEntityDeclHandler(parser->m_handlerArg, parser->m_declEntity->name, parser->m_declEntity->base, parser->m_declEntity->systemId, parser->m_declEntity->publicId, parser->m_declEntity->notation);
            handleDefault = 0;
          }

          else
            if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
            {
              *eventEndPP = s;
              parser->m_entityDeclHandler(parser->m_handlerArg, parser->m_declEntity->name, 0, ((const XML_Char *)NULL), 0, parser->m_declEntity->base, parser->m_declEntity->systemId, parser->m_declEntity->publicId, parser->m_declEntity->notation);
              handleDefault = 0;
            }

        }

      }

      signed int return_value$7=enc->predefinedEntityName(enc, s, next);
      if(!(return_value$7 == 0))
        parser->m_declEntity = ((ENTITY *)NULL);

      else
      {
        if(!(dtd->keepProcessing == 0))
        {
          const XML_Char *doProlog$$1$$3$$1$$3$$21$$2$$name;
          XML_Char *return_value_poolStoreString$4=poolStoreString(&dtd->pool, enc, s, next);
          doProlog$$1$$3$$1$$3$$21$$2$$name = return_value_poolStoreString$4;
          if(doProlog$$1$$3$$1$$3$$21$$2$$name == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          NAMED *return_value_lookup$3=lookup(parser, &dtd->generalEntities, doProlog$$1$$3$$1$$3$$21$$2$$name, sizeof(ENTITY) /*64ul*/ );
          parser->m_declEntity = (ENTITY *)return_value_lookup$3;
          if(parser->m_declEntity == ((ENTITY *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          if(!(parser->m_declEntity->name == doProlog$$1$$3$$1$$3$$21$$2$$name))
          {
            (&dtd->pool)->ptr = (&dtd->pool)->start;
            parser->m_declEntity = ((ENTITY *)NULL);
          }

          else
          {
            (&dtd->pool)->start = (&dtd->pool)->ptr;
            parser->m_declEntity->publicId = ((const XML_Char *)NULL);
            parser->m_declEntity->is_param = 0;
            __CPROVER_bool tmp_if_expr$16;
            if(!(parser->m_parentParser == ((XML_Parser)NULL)))
              tmp_if_expr$16 = 1;

            else
              tmp_if_expr$16 = parser->m_openInternalEntities != ((OPEN_INTERNAL_ENTITY *)NULL) ? 1 : 0;
            parser->m_declEntity->is_internal = (XML_Bool)!tmp_if_expr$16;
            if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
              handleDefault = 0;

          }
        }

        else
        {
          (&dtd->pool)->ptr = (&dtd->pool)->start;
          parser->m_declEntity = ((ENTITY *)NULL);
        }
        if(!(dtd->keepProcessing == 0))
        {
          const XML_Char *doProlog$$1$$3$$1$$3$$22$$name;
          XML_Char *return_value_poolStoreString$5=poolStoreString(&dtd->pool, enc, s, next);
          doProlog$$1$$3$$1$$3$$22$$name = return_value_poolStoreString$5;
          if(doProlog$$1$$3$$1$$3$$22$$name == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          NAMED *return_value_lookup$4=lookup(parser, &dtd->paramEntities, doProlog$$1$$3$$1$$3$$22$$name, sizeof(ENTITY) /*64ul*/ );
          parser->m_declEntity = (ENTITY *)return_value_lookup$4;
          if(parser->m_declEntity == ((ENTITY *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          if(!(parser->m_declEntity->name == doProlog$$1$$3$$1$$3$$22$$name))
          {
            (&dtd->pool)->ptr = (&dtd->pool)->start;
            parser->m_declEntity = ((ENTITY *)NULL);
          }

          else
          {
            (&dtd->pool)->start = (&dtd->pool)->ptr;
            parser->m_declEntity->publicId = ((const XML_Char *)NULL);
            parser->m_declEntity->is_param = 1;
            __CPROVER_bool tmp_if_expr$17;
            if(!(parser->m_parentParser == ((XML_Parser)NULL)))
              tmp_if_expr$17 = 1;

            else
              tmp_if_expr$17 = parser->m_openInternalEntities != ((OPEN_INTERNAL_ENTITY *)NULL) ? 1 : 0;
            parser->m_declEntity->is_internal = (XML_Bool)!tmp_if_expr$17;
            if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
              handleDefault = 0;

          }
        }

        else
        {
          (&dtd->pool)->ptr = (&dtd->pool)->start;
          parser->m_declEntity = ((ENTITY *)NULL);
        }
        parser->m_declNotationPublicId = ((const XML_Char *)NULL);
        parser->m_declNotationName = ((const XML_Char *)NULL);
        if(!(parser->m_notationDeclHandler == ((XML_NotationDeclHandler)NULL)))
        {
          XML_Char *return_value_poolStoreString$6=poolStoreString(&parser->m_tempPool, enc, s, next);
          parser->m_declNotationName = return_value_poolStoreString$6;
          if(parser->m_declNotationName == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
          handleDefault = 0;
        }

        signed int return_value$8=enc->isPublicId(enc, s, next, eventPP);
        if(return_value$8 == 0)
          return /*enum*/XML_ERROR_PUBLICID;

        if(!(parser->m_declNotationName == ((const XML_Char *)NULL)))
        {
          XML_Char *doProlog$$1$$3$$1$$3$$25$$tem;
          XML_Char *return_value_poolStoreString$7=poolStoreString(&parser->m_tempPool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
          doProlog$$1$$3$$1$$3$$25$$tem = return_value_poolStoreString$7;
          if(doProlog$$1$$3$$1$$3$$25$$tem == ((XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          normalizePublicId(doProlog$$1$$3$$1$$3$$25$$tem);
          parser->m_declNotationPublicId = doProlog$$1$$3$$1$$3$$25$$tem;
          (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
          handleDefault = 0;
        }

        if(!(parser->m_declNotationName == ((const XML_Char *)NULL)))
        {
          if(!(parser->m_notationDeclHandler == ((XML_NotationDeclHandler)NULL)))
          {
            const XML_Char *systemId;
            XML_Char *return_value_poolStoreString$8=poolStoreString(&parser->m_tempPool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
            systemId = return_value_poolStoreString$8;
            if(systemId == ((const XML_Char *)NULL))
              return /*enum*/XML_ERROR_NO_MEMORY;

            *eventEndPP = s;
            parser->m_notationDeclHandler(parser->m_handlerArg, parser->m_declNotationName, parser->m_curBase, systemId, parser->m_declNotationPublicId);
            handleDefault = 0;
          }

        }

        poolClear(&parser->m_tempPool);
        if(!(parser->m_declNotationPublicId == ((const XML_Char *)NULL)))
        {
          if(!(parser->m_notationDeclHandler == ((XML_NotationDeclHandler)NULL)))
          {
            *eventEndPP = s;
            parser->m_notationDeclHandler(parser->m_handlerArg, parser->m_declNotationName, parser->m_curBase, ((const XML_Char *)NULL), parser->m_declNotationPublicId);
            handleDefault = 0;
          }

        }

        poolClear(&parser->m_tempPool);
        if(tok == 28)
        {
          return /*enum*/XML_ERROR_PARAM_ENTITY_REF;
          return /*enum*/XML_ERROR_MISPLACED_XML_PI;
        }

        return /*enum*/XML_ERROR_SYNTAX;
        enum XML_Error doProlog$$1$$3$$1$$3$$29$$result;
        if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
          reportDefault(parser, enc, s, next);

        handleDefault = 0;
        doProlog$$1$$3$$1$$3$$29$$result=doIgnoreSection(parser, enc, &next, end, nextPtr, haveMore);
        if(!((signed int)doProlog$$1$$3$$1$$3$$29$$result == 0))
          return doProlog$$1$$3$$1$$3$$29$$result;

        else
          if(next == ((const char *)NULL))
          {
            parser->m_processor = ignoreSectionProcessor;
            return doProlog$$1$$3$$1$$3$$29$$result;
          }

        if(parser->m_prologState.level >= parser->m_groupSize)
        {
          if(!(parser->m_groupSize == 0u))
          {
            if(parser->m_groupSize >= 2147483648u)
              return /*enum*/XML_ERROR_NO_MEMORY;

            char *new_connector;
            unsigned int tmp_assign=parser->m_groupSize * 2u;
            parser->m_groupSize = tmp_assign;
            void *return_value$9=parser->m_mem.realloc_fcn((void *)parser->m_groupConnector, (size_t)tmp_assign);
            new_connector = (char *)return_value$9;
            if(new_connector == ((char *)NULL))
            {
              parser->m_groupSize = parser->m_groupSize / 2u;
              return /*enum*/XML_ERROR_NO_MEMORY;
            }

            parser->m_groupConnector = new_connector;
            if(!(dtd->scaffIndex == ((signed int *)NULL)))
            {
              signed int *new_scaff_index;
              void *return_value$10=parser->m_mem.realloc_fcn((void *)dtd->scaffIndex, (unsigned long int)parser->m_groupSize * sizeof(signed int) /*4ul*/ );
              new_scaff_index = (signed int *)return_value$10;
              if(new_scaff_index == ((signed int *)NULL))
                return /*enum*/XML_ERROR_NO_MEMORY;

              dtd->scaffIndex = new_scaff_index;
            }

          }

          else
          {
            unsigned int tmp_assign$0=32u;
            parser->m_groupSize = tmp_assign$0;
            void *return_value$11=parser->m_mem.malloc_fcn((size_t)tmp_assign$0);
            parser->m_groupConnector = (char *)return_value$11;
            if(parser->m_groupConnector == ((char *)NULL))
            {
              parser->m_groupSize = 0u;
              return /*enum*/XML_ERROR_NO_MEMORY;
            }

          }
        }

        parser->m_groupConnector[(signed long int)parser->m_prologState.level] = 0;
        if(!(dtd->in_eldecl == 0))
        {
          signed int myindex;
          signed int return_value_nextScaffoldPart=nextScaffoldPart(parser);
          myindex = return_value_nextScaffoldPart;
          if(!(myindex >= 0))
            return /*enum*/XML_ERROR_NO_MEMORY;

          (void)sizeof(signed int) /*4ul*/ ;
          /* assertion dtd->scaffIndex != NULL */
          assert(dtd->scaffIndex != ((signed int *)NULL));
          dtd->scaffIndex[(signed long int)dtd->scaffLevel] = myindex;
          dtd->scaffLevel = dtd->scaffLevel + 1;
          (dtd->scaffold + (signed long int)myindex)->type = /*enum*/XML_CTYPE_SEQ;
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
            handleDefault = 0;

        }

        if((signed int)parser->m_groupConnector[(signed long int)parser->m_prologState.level] == 0x7C)
          return /*enum*/XML_ERROR_SYNTAX;

        parser->m_groupConnector[(signed long int)parser->m_prologState.level] = ',';
        if(!(dtd->in_eldecl == 0))
        {
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
            handleDefault = 0;

        }

        if((signed int)parser->m_groupConnector[(signed long int)parser->m_prologState.level] == 0x2C)
          return /*enum*/XML_ERROR_SYNTAX;

        if(!(dtd->in_eldecl == 0))
        {
          if(parser->m_groupConnector[(signed long int)parser->m_prologState.level] == 0)
          {
            if(!((signed int)(dtd->scaffold + (signed long int)dtd->scaffIndex[(signed long int)(dtd->scaffLevel + -1)])->type == 3))
            {
              (dtd->scaffold + (signed long int)dtd->scaffIndex[(signed long int)(dtd->scaffLevel - 1)])->type = /*enum*/XML_CTYPE_CHOICE;
              if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
                handleDefault = 0;

            }

          }

        }

        parser->m_groupConnector[(signed long int)parser->m_prologState.level] = '|';
        dtd->hasParamEntityRefs = 1;
        if(parser->m_paramEntityParsing == /*enum*/XML_PARAM_ENTITY_PARSING_NEVER)
          dtd->keepProcessing = dtd->standalone;

        else
        {
          const XML_Char *doProlog$$1$$3$$1$$3$$33$$name;
          ENTITY *doProlog$$1$$3$$1$$3$$33$$entity;
          doProlog$$1$$3$$1$$3$$33$$name=poolStoreString(&dtd->pool, enc, s + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
          if(doProlog$$1$$3$$1$$3$$33$$name == ((const XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          NAMED *return_value_lookup$5=lookup(parser, &dtd->paramEntities, doProlog$$1$$3$$1$$3$$33$$name, 0ul);
          doProlog$$1$$3$$1$$3$$33$$entity = (ENTITY *)return_value_lookup$5;
          (&dtd->pool)->ptr = (&dtd->pool)->start;
          __CPROVER_bool tmp_if_expr$19;
          if(!(parser->m_prologState.documentEntity == 0))
          {
            if(!(dtd->standalone == 0))
              tmp_if_expr$18 = !(parser->m_openInternalEntities != ((OPEN_INTERNAL_ENTITY *)NULL));

            else
              tmp_if_expr$18 = !(dtd->hasParamEntityRefs != 0);
            tmp_if_expr$19 = tmp_if_expr$18 ? 1 : 0;
          }

          else
            tmp_if_expr$19 = 0;
          if(tmp_if_expr$19)
          {
            if(doProlog$$1$$3$$1$$3$$33$$entity == ((ENTITY *)NULL))
              return /*enum*/XML_ERROR_UNDEFINED_ENTITY;

            else
              if(doProlog$$1$$3$$1$$3$$33$$entity->is_internal == 0)
                return /*enum*/XML_ERROR_ENTITY_DECLARED_IN_PE;

          }

          else
            if(doProlog$$1$$3$$1$$3$$33$$entity == ((ENTITY *)NULL))
            {
              dtd->keepProcessing = dtd->standalone;
              if(role == 60)
              {
                if(!(parser->m_skippedEntityHandler == ((XML_SkippedEntityHandler)NULL)))
                {
                  parser->m_skippedEntityHandler(parser->m_handlerArg, doProlog$$1$$3$$1$$3$$33$$name, 1);
                  handleDefault = 0;
                }

              }

            }

          if(!(doProlog$$1$$3$$1$$3$$33$$entity->open == 0))
            return /*enum*/XML_ERROR_RECURSIVE_ENTITY_REF;

          if(!(doProlog$$1$$3$$1$$3$$33$$entity->textPtr == ((const XML_Char *)NULL)))
          {
            enum XML_Error doProlog$$1$$3$$1$$3$$33$$3$$result;
            XML_Bool betweenDecl=role == 60 ? 1 : 0;
            doProlog$$1$$3$$1$$3$$33$$3$$result=processInternalEntity(parser, doProlog$$1$$3$$1$$3$$33$$entity, betweenDecl);
            if(!((signed int)doProlog$$1$$3$$1$$3$$33$$3$$result == 0))
              return doProlog$$1$$3$$1$$3$$33$$3$$result;

            handleDefault = 0;
          }

          if(!(parser->m_externalEntityRefHandler == ((XML_ExternalEntityRefHandler)NULL)))
          {
            dtd->paramEntityRead = 0;
            doProlog$$1$$3$$1$$3$$33$$entity->open = 1;
            entityTrackingOnOpen(parser, doProlog$$1$$3$$1$$3$$33$$entity, 5303);
            signed int return_value$12=parser->m_externalEntityRefHandler(parser->m_externalEntityRefHandlerArg, ((const XML_Char *)NULL), doProlog$$1$$3$$1$$3$$33$$entity->base, doProlog$$1$$3$$1$$3$$33$$entity->systemId, doProlog$$1$$3$$1$$3$$33$$entity->publicId);
            if(return_value$12 == 0)
            {
              entityTrackingOnClose(parser, doProlog$$1$$3$$1$$3$$33$$entity, 5307);
              doProlog$$1$$3$$1$$3$$33$$entity->open = 0;
              return /*enum*/XML_ERROR_EXTERNAL_ENTITY_HANDLING;
            }

            entityTrackingOnClose(parser, doProlog$$1$$3$$1$$3$$33$$entity, 5311);
            doProlog$$1$$3$$1$$3$$33$$entity->open = 0;
            handleDefault = 0;
            if(dtd->paramEntityRead == 0)
              dtd->keepProcessing = dtd->standalone;

          }

          else
            dtd->keepProcessing = dtd->standalone;
        }
        if(dtd->standalone == 0)
        {
          if(!(parser->m_notStandaloneHandler == ((XML_NotStandaloneHandler)NULL)))
          {
            return_value$13=parser->m_notStandaloneHandler(parser->m_handlerArg);
            if(return_value$13 == 0)
              return /*enum*/XML_ERROR_NOT_STANDALONE;

          }

        }

        if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
        {
          ELEMENT_TYPE *return_value_getElementType$0=getElementType(parser, enc, s, next);
          parser->m_declElementType = return_value_getElementType$0;
          if(parser->m_declElementType == ((ELEMENT_TYPE *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          dtd->scaffLevel = 0;
          dtd->scaffCount = 0u;
          dtd->in_eldecl = 1;
          handleDefault = 0;
        }

        if(!(dtd->in_eldecl == 0))
        {
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
          {
            XML_Content *content;
            void *return_value$14=parser->m_mem.malloc_fcn(sizeof(XML_Content) /*32ul*/ );
            content = (XML_Content *)return_value$14;
            if(content == ((XML_Content *)NULL))
              return /*enum*/XML_ERROR_NO_MEMORY;

            content->quant = /*enum*/XML_CQUANT_NONE;
            content->name = ((XML_Char *)NULL);
            content->numchildren = 0u;
            content->children = ((XML_Content *)NULL);
            content->type = (enum XML_Content_Type)(role == 41 ? 2 : 1);
            *eventEndPP = s;
            parser->m_elementDeclHandler(parser->m_handlerArg, parser->m_declElementType->name, content);
            handleDefault = 0;
          }

          dtd->in_eldecl = 0;
        }

        if(!(dtd->in_eldecl == 0))
        {
          (dtd->scaffold + (signed long int)dtd->scaffIndex[(signed long int)(dtd->scaffLevel - 1)])->type = /*enum*/XML_CTYPE_MIXED;
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
            handleDefault = 0;

        }

        quant = /*enum*/XML_CQUANT_NONE;
        quant = /*enum*/XML_CQUANT_OPT;
        quant = /*enum*/XML_CQUANT_REP;
        quant = /*enum*/XML_CQUANT_PLUS;

      elementContent:
        ;
        if(!(dtd->in_eldecl == 0))
        {
          ELEMENT_TYPE *el;
          const XML_Char *name;
          size_t nameLen;
          const char *nxt;
          const char *tmp_if_expr$20;
          if((signed int)quant == 0)
            tmp_if_expr$20 = next;

          else
            tmp_if_expr$20 = next - (signed long int)enc->minBytesPerChar;
          nxt = tmp_if_expr$20;
          signed int doProlog$$1$$3$$1$$3$$37$$myindex;
          signed int return_value_nextScaffoldPart$0=nextScaffoldPart(parser);
          doProlog$$1$$3$$1$$3$$37$$myindex = return_value_nextScaffoldPart$0;
          if(!(doProlog$$1$$3$$1$$3$$37$$myindex >= 0))
            return /*enum*/XML_ERROR_NO_MEMORY;

          (dtd->scaffold + (signed long int)doProlog$$1$$3$$1$$3$$37$$myindex)->type = /*enum*/XML_CTYPE_NAME;
          (dtd->scaffold + (signed long int)doProlog$$1$$3$$1$$3$$37$$myindex)->quant = quant;
          el=getElementType(parser, enc, s, nxt);
          if(el == ((ELEMENT_TYPE *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          name = el->name;
          (dtd->scaffold + (signed long int)doProlog$$1$$3$$1$$3$$37$$myindex)->name = name;
          nameLen = 0ul;
          size_t tmp_post$3=nameLen;
          nameLen = nameLen + 1ul;
          if(!((unsigned long int)(4294967295u + -dtd->contentStringLen) >= nameLen))
            return /*enum*/XML_ERROR_NO_MEMORY;

          dtd->contentStringLen = dtd->contentStringLen + (unsigned int)nameLen;
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
            handleDefault = 0;

        }

        quant = /*enum*/XML_CQUANT_NONE;
        quant = /*enum*/XML_CQUANT_OPT;
        quant = /*enum*/XML_CQUANT_REP;
        quant = /*enum*/XML_CQUANT_PLUS;

      closeGroup:
        ;
        if(!(dtd->in_eldecl == 0))
        {
          if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
            handleDefault = 0;

          dtd->scaffLevel = dtd->scaffLevel - 1;
          (dtd->scaffold + (signed long int)dtd->scaffIndex[(signed long int)dtd->scaffLevel])->quant = quant;
          if(dtd->scaffLevel == 0)
          {
            if(handleDefault == 0)
            {
              XML_Content *model;
              XML_Content *return_value_build_model=build_model(parser);
              model = return_value_build_model;
              if(model == ((XML_Content *)NULL))
                return /*enum*/XML_ERROR_NO_MEMORY;

              *eventEndPP = s;
              parser->m_elementDeclHandler(parser->m_handlerArg, parser->m_declElementType->name, model);
            }

            dtd->in_eldecl = 0;
            dtd->contentStringLen = 0u;
          }

        }

        signed int return_value_reportProcessingInstruction=reportProcessingInstruction(parser, enc, s, next);
        if(return_value_reportProcessingInstruction == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

        handleDefault = 0;
        signed int return_value_reportComment=reportComment(parser, enc, s, next);
        if(return_value_reportComment == 0)
          return /*enum*/XML_ERROR_NO_MEMORY;

        handleDefault = 0;
        if(tok == 14)
          handleDefault = 0;

        if(!(parser->m_startDoctypeDeclHandler == ((XML_StartDoctypeDeclHandler)NULL)))
          handleDefault = 0;

        if(!(dtd->keepProcessing == 0))
        {
          if(!(parser->m_entityDeclHandler == ((XML_EntityDeclHandler)NULL)))
            handleDefault = 0;

        }

        if(!(parser->m_notationDeclHandler == ((XML_NotationDeclHandler)NULL)))
          handleDefault = 0;

        if(!(dtd->keepProcessing == 0))
        {
          if(!(parser->m_attlistDeclHandler == ((XML_AttlistDeclHandler)NULL)))
            handleDefault = 0;

        }

        if(!(parser->m_elementDeclHandler == ((XML_ElementDeclHandler)NULL)))
          handleDefault = 0;

      }
    }

    if(!(handleDefault == 0))
    {
      if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
        reportDefault(parser, enc, s, next);

    }

    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    if(tmp_switch_value == 3)
    {
      *nextPtr = next;
      return /*enum*/XML_ERROR_NONE;
      return /*enum*/XML_ERROR_ABORTED;
    }

    s = next;
    tok=enc->scanners[0l](enc, s, end, &next);
  }
}

// dtdCopy
// file xmlparse.c line 6667
static signed int dtdCopy(XML_Parser oldParser, DTD *newDtd, const DTD *oldDtd, const XML_Memory_Handling_Suite *ms)
{
  HASH_TABLE_ITER iter;
  hashTableIterInit(&iter, &oldDtd->prefixes);
  while(1)
  {
    const XML_Char *name;
    const PREFIX *oldP;
    NAMED *return_value_hashTableIterNext=hashTableIterNext(&iter);
    oldP = (PREFIX *)return_value_hashTableIterNext;
    if(oldP == ((const PREFIX *)NULL))
      break;

    name=poolCopyString(&newDtd->pool, oldP->name);
    if(name == ((const XML_Char *)NULL))
      return 0;

    NAMED *return_value_lookup=lookup(oldParser, &newDtd->prefixes, name, sizeof(PREFIX) /*16ul*/ );
    if(return_value_lookup == ((NAMED *)NULL))
      return 0;

  }
  hashTableIterInit(&iter, &oldDtd->attributeIds);
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  NAMED *return_value_lookup$1;
  while(1)
  {
    ATTRIBUTE_ID *newA;
    const XML_Char *dtdCopy$$1$$2$$1$$name;
    const ATTRIBUTE_ID *oldA;
    NAMED *return_value_hashTableIterNext$0=hashTableIterNext(&iter);
    oldA = (ATTRIBUTE_ID *)return_value_hashTableIterNext$0;
    if(oldA == ((const ATTRIBUTE_ID *)NULL))
      break;

    __CPROVER_bool tmp_if_expr;
    if(newDtd->pool.ptr == newDtd->pool.end)
    {
      return_value_poolGrow=poolGrow(&newDtd->pool);
      tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post = (&newDtd->pool)->ptr;
      (&newDtd->pool)->ptr = (&newDtd->pool)->ptr + 1l;
      *tmp_post = 0;
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return 0;

    dtdCopy$$1$$2$$1$$name=poolCopyString(&newDtd->pool, oldA->name);
    if(dtdCopy$$1$$2$$1$$name == ((const XML_Char *)NULL))
      return 0;

    dtdCopy$$1$$2$$1$$name = dtdCopy$$1$$2$$1$$name + 1l;
    NAMED *return_value_lookup$0=lookup(oldParser, &newDtd->attributeIds, dtdCopy$$1$$2$$1$$name, sizeof(ATTRIBUTE_ID) /*24ul*/ );
    newA = (ATTRIBUTE_ID *)return_value_lookup$0;
    if(newA == ((ATTRIBUTE_ID *)NULL))
      return 0;

    newA->maybeTokenized = oldA->maybeTokenized;
    if(!(oldA->prefix == ((PREFIX *)NULL)))
    {
      newA->xmlns = oldA->xmlns;
      if(oldA->prefix == &oldDtd->defaultPrefix)
        newA->prefix = &newDtd->defaultPrefix;

      else
      {
        return_value_lookup$1=lookup(oldParser, &newDtd->prefixes, oldA->prefix->name, 0ul);
        newA->prefix = (PREFIX *)return_value_lookup$1;
      }
    }

  }
  hashTableIterInit(&iter, &oldDtd->elementTypes);
  NAMED *return_value_lookup$3;
  NAMED *return_value_lookup$4;
  while(1)
  {
    signed int i;
    ELEMENT_TYPE *newE;
    const XML_Char *dtdCopy$$1$$3$$1$$name;
    const ELEMENT_TYPE *oldE;
    NAMED *return_value_hashTableIterNext$1=hashTableIterNext(&iter);
    oldE = (ELEMENT_TYPE *)return_value_hashTableIterNext$1;
    if(oldE == ((const ELEMENT_TYPE *)NULL))
      break;

    dtdCopy$$1$$3$$1$$name=poolCopyString(&newDtd->pool, oldE->name);
    if(dtdCopy$$1$$3$$1$$name == ((const XML_Char *)NULL))
      return 0;

    NAMED *return_value_lookup$2=lookup(oldParser, &newDtd->elementTypes, dtdCopy$$1$$3$$1$$name, sizeof(ELEMENT_TYPE) /*40ul*/ );
    newE = (ELEMENT_TYPE *)return_value_lookup$2;
    if(newE == ((ELEMENT_TYPE *)NULL))
      return 0;

    if(!(oldE->nDefaultAtts == 0))
    {
      void *return_value=ms->malloc_fcn((unsigned long int)oldE->nDefaultAtts * sizeof(DEFAULT_ATTRIBUTE) /*24ul*/ );
      newE->defaultAtts = (DEFAULT_ATTRIBUTE *)return_value;
      if(newE->defaultAtts == ((DEFAULT_ATTRIBUTE *)NULL))
        return 0;

    }

    if(!(oldE->idAtt == ((const ATTRIBUTE_ID *)NULL)))
    {
      return_value_lookup$3=lookup(oldParser, &newDtd->attributeIds, oldE->idAtt->name, 0ul);
      newE->idAtt = (ATTRIBUTE_ID *)return_value_lookup$3;
    }

    const signed int tmp_assign=oldE->nDefaultAtts;
    newE->nDefaultAtts = tmp_assign;
    newE->allocDefaultAtts = tmp_assign;
    if(!(oldE->prefix == ((PREFIX *)NULL)))
    {
      return_value_lookup$4=lookup(oldParser, &newDtd->prefixes, oldE->prefix->name, 0ul);
      newE->prefix = (PREFIX *)return_value_lookup$4;
    }

    i = 0;
    for( ; !(i >= newE->nDefaultAtts); i = i + 1)
    {
      NAMED *return_value_lookup$5=lookup(oldParser, &newDtd->attributeIds, (oldE->defaultAtts + (signed long int)i)->id->name, 0ul);
      (newE->defaultAtts + (signed long int)i)->id = (ATTRIBUTE_ID *)return_value_lookup$5;
      (newE->defaultAtts + (signed long int)i)->isCdata = (oldE->defaultAtts + (signed long int)i)->isCdata;
      if(!((oldE->defaultAtts + (signed long int)i)->value == ((const XML_Char *)NULL)))
      {
        const XML_Char *return_value_poolCopyString=poolCopyString(&newDtd->pool, (oldE->defaultAtts + (signed long int)i)->value);
        (newE->defaultAtts + (signed long int)i)->value = return_value_poolCopyString;
        if((newE->defaultAtts + (signed long int)i)->value == ((const XML_Char *)NULL))
          return 0;

      }

      else
        (newE->defaultAtts + (signed long int)i)->value = ((const XML_Char *)NULL);
    }
  }
  signed int return_value_copyEntityTable=copyEntityTable(oldParser, &newDtd->generalEntities, &newDtd->pool, &oldDtd->generalEntities);
  if(return_value_copyEntityTable == 0)
    return 0;

  else
  {
    signed int return_value_copyEntityTable$0=copyEntityTable(oldParser, &newDtd->paramEntities, &newDtd->pool, &oldDtd->paramEntities);
    if(return_value_copyEntityTable$0 == 0)
      return 0;

    else
    {
      newDtd->paramEntityRead = oldDtd->paramEntityRead;
      newDtd->keepProcessing = oldDtd->keepProcessing;
      newDtd->hasParamEntityRefs = oldDtd->hasParamEntityRefs;
      newDtd->standalone = oldDtd->standalone;
      newDtd->in_eldecl = oldDtd->in_eldecl;
      newDtd->scaffold = oldDtd->scaffold;
      newDtd->contentStringLen = oldDtd->contentStringLen;
      newDtd->scaffSize = oldDtd->scaffSize;
      newDtd->scaffLevel = oldDtd->scaffLevel;
      newDtd->scaffIndex = oldDtd->scaffIndex;
      return 1;
    }
  }
}

// dtdCreate
// file xmlparse.c line 6564
static DTD * dtdCreate(const XML_Memory_Handling_Suite *ms)
{
  DTD *p;
  void *return_value=ms->malloc_fcn(sizeof(DTD) /*360ul*/ );
  p = (DTD *)return_value;
  if(p == ((DTD *)NULL))
    return p;

  else
  {
    poolInit(&p->pool, ms);
    poolInit(&p->entityValuePool, ms);
    hashTableInit(&p->generalEntities, ms);
    hashTableInit(&p->elementTypes, ms);
    hashTableInit(&p->attributeIds, ms);
    hashTableInit(&p->prefixes, ms);
    p->paramEntityRead = 0;
    hashTableInit(&p->paramEntities, ms);
    p->defaultPrefix.name = ((const XML_Char *)NULL);
    p->defaultPrefix.binding = ((BINDING *)NULL);
    p->in_eldecl = 0;
    p->scaffIndex = ((signed int *)NULL);
    p->scaffold = ((CONTENT_SCAFFOLD *)NULL);
    p->scaffLevel = 0;
    p->scaffSize = 0u;
    p->scaffCount = 0u;
    p->contentStringLen = 0u;
    p->keepProcessing = 1;
    p->hasParamEntityRefs = 0;
    p->standalone = 0;
    return p;
  }
}

// dtdDestroy
// file xmlparse.c line 6637
static void dtdDestroy(DTD *p, XML_Bool isDocEntity, const XML_Memory_Handling_Suite *ms)
{
  HASH_TABLE_ITER iter;
  hashTableIterInit(&iter, &p->elementTypes);
  while(1)
  {
    ELEMENT_TYPE *e;
    NAMED *return_value_hashTableIterNext=hashTableIterNext(&iter);
    e = (ELEMENT_TYPE *)return_value_hashTableIterNext;
    if(e == ((ELEMENT_TYPE *)NULL))
      break;

    if(!(e->allocDefaultAtts == 0))
      ms->free_fcn((void *)e->defaultAtts);

  }
  hashTableDestroy(&p->generalEntities);
  hashTableDestroy(&p->paramEntities);
  hashTableDestroy(&p->elementTypes);
  hashTableDestroy(&p->attributeIds);
  hashTableDestroy(&p->prefixes);
  poolDestroy(&p->pool);
  poolDestroy(&p->entityValuePool);
  if(!(isDocEntity == 0))
  {
    ms->free_fcn((void *)p->scaffIndex);
    ms->free_fcn((void *)p->scaffold);
  }

  ms->free_fcn((void *)p);
}

// dtdReset
// file xmlparse.c line 6596
static void dtdReset(DTD *p, const XML_Memory_Handling_Suite *ms)
{
  HASH_TABLE_ITER iter;
  hashTableIterInit(&iter, &p->elementTypes);
  while(1)
  {
    ELEMENT_TYPE *e;
    NAMED *return_value_hashTableIterNext=hashTableIterNext(&iter);
    e = (ELEMENT_TYPE *)return_value_hashTableIterNext;
    if(e == ((ELEMENT_TYPE *)NULL))
      break;

    if(!(e->allocDefaultAtts == 0))
      ms->free_fcn((void *)e->defaultAtts);

  }
  hashTableClear(&p->generalEntities);
  p->paramEntityRead = 0;
  hashTableClear(&p->paramEntities);
  hashTableClear(&p->elementTypes);
  hashTableClear(&p->attributeIds);
  hashTableClear(&p->prefixes);
  poolClear(&p->pool);
  poolClear(&p->entityValuePool);
  p->defaultPrefix.name = ((const XML_Char *)NULL);
  p->defaultPrefix.binding = ((BINDING *)NULL);
  p->in_eldecl = 0;
  ms->free_fcn((void *)p->scaffIndex);
  p->scaffIndex = ((signed int *)NULL);
  ms->free_fcn((void *)p->scaffold);
  p->scaffold = ((CONTENT_SCAFFOLD *)NULL);
  p->scaffLevel = 0;
  p->scaffSize = 0u;
  p->scaffCount = 0u;
  p->contentStringLen = 0u;
  p->keepProcessing = 1;
  p->hasParamEntityRefs = 0;
  p->standalone = 0;
}

// entityTrackingOnClose
// file xmlparse.c line 7676
static void entityTrackingOnClose(XML_Parser originParser, ENTITY *entity, signed int sourceLine)
{
  XML_Parser rootParser;
  XML_Parser return_value_getRootParserOf=getRootParserOf(originParser, ((unsigned int *)NULL));
  rootParser = return_value_getRootParserOf;
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  entityTrackingReportStats(rootParser, entity, "CLOSE", sourceLine);
  rootParser->m_entity_stats.currentDepth = rootParser->m_entity_stats.currentDepth - 1u;
}

// entityTrackingOnOpen
// file xmlparse.c line 7661
static void entityTrackingOnOpen(XML_Parser originParser, ENTITY *entity, signed int sourceLine)
{
  XML_Parser rootParser;
  XML_Parser return_value_getRootParserOf=getRootParserOf(originParser, ((unsigned int *)NULL));
  rootParser = return_value_getRootParserOf;
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  rootParser->m_entity_stats.countEverOpened = rootParser->m_entity_stats.countEverOpened + 1u;
  rootParser->m_entity_stats.currentDepth = rootParser->m_entity_stats.currentDepth + 1u;
  if(!(rootParser->m_entity_stats.maximumDepthSeen >= rootParser->m_entity_stats.currentDepth))
    rootParser->m_entity_stats.maximumDepthSeen = rootParser->m_entity_stats.maximumDepthSeen + 1u;

  entityTrackingReportStats(rootParser, entity, "OPEN ", sourceLine);
}

// entityTrackingReportStats
// file xmlparse.c line 7637
static void entityTrackingReportStats(XML_Parser rootParser, ENTITY *entity, const char *action, signed int sourceLine)
{
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  if(rootParser->m_entity_stats.debugLevel >= 1)
  {
    const char * const entityName=entity->name;
    fprintf(stderr, "expat: Entities(%p): Count %9d, depth %2d/%2d %*s%s%s; %s length %d (xmlparse.c:%d)\n", (void *)rootParser, rootParser->m_entity_stats.countEverOpened, rootParser->m_entity_stats.currentDepth, rootParser->m_entity_stats.maximumDepthSeen, (rootParser->m_entity_stats.currentDepth - 1u) * 2u, (const void *)"", entity->is_param != 0 ? "%" : "&", entityName, action, entity->textLen, sourceLine);
  }

}

// entityValueInitProcessor
// file xmlparse.c line 4299
static enum XML_Error entityValueInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  signed int tok;
  const char *start=s;
  const char *next=start;
  parser->m_eventPtr = start;
  __CPROVER_bool tmp_if_expr;
  tok=parser->m_encoding->scanners[0l](parser->m_encoding, start, end, &next);
  parser->m_eventEndPtr = next;
  if(!(tok >= 1))
  {
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      if(!(tok == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

    }

    if(tok == 0)
    {
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
      return /*enum*/XML_ERROR_PARTIAL_CHAR;
    }

    enum XML_Error return_value_storeEntityValue=storeEntityValue(parser, parser->m_encoding, s, end, /*enum*/XML_ACCOUNT_DIRECT);
    return return_value_storeEntityValue;
  }

  else
    if(tok == 12)
    {
      enum XML_Error result=processXmlDecl(parser, 0, start, next);
      if(!((signed int)result == 0))
        return result;

      if((signed int)parser->m_parsingStatus.parsing == 2)
        return /*enum*/XML_ERROR_ABORTED;

      *nextPtr = next;
      parser->m_processor = entityValueProcessor;
      enum XML_Error return_value_entityValueProcessor=entityValueProcessor(parser, next, end, nextPtr);
      return return_value_entityValueProcessor;
    }

    else
    {
      if(tok == 14 && next == end)
        tmp_if_expr = !(parser->m_parsingStatus.finalBuffer != 0) ? 1 : 0;

      else
        tmp_if_expr = 0;
      if(tmp_if_expr)
      {
        XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 4359, /*enum*/XML_ACCOUNT_DIRECT);
        if(return_value_accountingDiffTolerated == 0)
        {
          accountingOnAbort(parser);
          return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
        }

        *nextPtr = next;
        return /*enum*/XML_ERROR_NONE;
      }

      else
        if(tok == 29)
        {
          *nextPtr = next;
          return /*enum*/XML_ERROR_SYNTAX;
        }

    }
  start = next;
  parser->m_eventPtr = start;
}

// entityValueProcessor
// file xmlparse.c line 4429
static enum XML_Error entityValueProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  const char *start=s;
  const char *next=s;
  const ENCODING *enc=parser->m_encoding;
  signed int tok;
  tok=enc->scanners[0l](enc, start, end, &next);
  if(!(tok >= 1))
  {
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      if(!(tok == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

    }

    if(tok == 0)
    {
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
      return /*enum*/XML_ERROR_PARTIAL_CHAR;
    }

    enum XML_Error return_value_storeEntityValue=storeEntityValue(parser, enc, s, end, /*enum*/XML_ACCOUNT_DIRECT);
    return return_value_storeEntityValue;
  }

  start = next;
}

// epilogProcessor
// file xmlparse.c line 5508
static enum XML_Error epilogProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  parser->m_processor = epilogProcessor;
  parser->m_eventPtr = s;
  signed int return_value_reportProcessingInstruction;
  signed int return_value_reportComment;
  {
    const char *next=((const char *)NULL);
    signed int tok;
    signed int return_value=parser->m_encoding->scanners[0l](parser->m_encoding, s, end, &next);
    tok = return_value;
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 5516, /*enum*/XML_ACCOUNT_DIRECT);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    parser->m_eventEndPtr = next;
    if(tok == -15)
    {
      if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
      {
        reportDefault(parser, parser->m_encoding, s, next);
        if((signed int)parser->m_parsingStatus.parsing == 2)
          return /*enum*/XML_ERROR_ABORTED;

      }

      *nextPtr = next;
      return /*enum*/XML_ERROR_NONE;
      *nextPtr = s;
      return /*enum*/XML_ERROR_NONE;
      if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
        reportDefault(parser, parser->m_encoding, s, next);

      return_value_reportProcessingInstruction=reportProcessingInstruction(parser, parser->m_encoding, s, next);
      if(return_value_reportProcessingInstruction == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

      return_value_reportComment=reportComment(parser, parser->m_encoding, s, next);
      if(return_value_reportComment == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

      parser->m_eventPtr = next;
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      if(parser->m_parsingStatus.finalBuffer == 0)
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
      if(parser->m_parsingStatus.finalBuffer == 0)
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

      return /*enum*/XML_ERROR_PARTIAL_CHAR;
    }

    return /*enum*/XML_ERROR_JUNK_AFTER_DOC_ELEMENT;
    s = next;
    parser->m_eventPtr = s;
    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    if(tmp_switch_value == 3)
    {
      *nextPtr = next;
      return /*enum*/XML_ERROR_NONE;
      return /*enum*/XML_ERROR_ABORTED;
    }

  }
}

// errorProcessor
// file xmlparse.c line 5710
static enum XML_Error errorProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  (void)s;
  (void)end;
  (void)nextPtr;
  return parser->m_errorCode;
}

// externalEntityContentProcessor
// file xmlparse.c line 2723
static enum XML_Error externalEntityContentProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_doContent=doContent(parser, 1, parser->m_encoding, start, end, endPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
  result = return_value_doContent;
  if((signed int)result == 0)
  {
    XML_Bool return_value_storeRawNames=storeRawNames(parser);
    if(return_value_storeRawNames == 0)
      return /*enum*/XML_ERROR_NO_MEMORY;

  }

  return result;
}

// externalEntityInitProcessor
// file xmlparse.c line 2621
static enum XML_Error externalEntityInitProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_initializeEncoding=initializeEncoding(parser);
  result = return_value_initializeEncoding;
  if(!((signed int)result == 0))
    return result;

  else
  {
    parser->m_processor = externalEntityInitProcessor2;
    enum XML_Error return_value_externalEntityInitProcessor2=externalEntityInitProcessor2(parser, start, end, endPtr);
    return return_value_externalEntityInitProcessor2;
  }
}

// externalEntityInitProcessor2
// file xmlparse.c line 2631
static enum XML_Error externalEntityInitProcessor2(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  const char *next=start;
  signed int tok;
  signed int return_value=parser->m_encoding->scanners[1l](parser->m_encoding, start, end, &next);
  tok = return_value;
  if(tok == 14)
  {
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, start, next, 2638, /*enum*/XML_ACCOUNT_DIRECT);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    if(next == end)
    {
      if(parser->m_parsingStatus.finalBuffer == 0)
      {
        *endPtr = next;
        return /*enum*/XML_ERROR_NONE;
      }

    }

    start = next;
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      *endPtr = start;
      return /*enum*/XML_ERROR_NONE;
    }

    parser->m_eventPtr = start;
    return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      *endPtr = start;
      return /*enum*/XML_ERROR_NONE;
    }

    parser->m_eventPtr = start;
    return /*enum*/XML_ERROR_PARTIAL_CHAR;
  }

  parser->m_processor = externalEntityInitProcessor3;
  enum XML_Error return_value_externalEntityInitProcessor3=externalEntityInitProcessor3(parser, start, end, endPtr);
  return return_value_externalEntityInitProcessor3;
}

// externalEntityInitProcessor3
// file xmlparse.c line 2676
static enum XML_Error externalEntityInitProcessor3(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  signed int tok;
  const char *next=start;
  parser->m_eventPtr = start;
  tok=parser->m_encoding->scanners[1l](parser->m_encoding, start, end, &next);
  parser->m_eventEndPtr = next;
  if(tok == 12)
  {
    enum XML_Error result=processXmlDecl(parser, 1, start, next);
    if(!((signed int)result == 0))
      return result;

    signed int tmp_switch_value=(signed int)parser->m_parsingStatus.parsing;
    if(tmp_switch_value == 3)
    {
      *endPtr = next;
      return /*enum*/XML_ERROR_NONE;
      return /*enum*/XML_ERROR_ABORTED;
    }

    start = next;
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      *endPtr = start;
      return /*enum*/XML_ERROR_NONE;
    }

    return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      *endPtr = start;
      return /*enum*/XML_ERROR_NONE;
    }

    return /*enum*/XML_ERROR_PARTIAL_CHAR;
  }

  parser->m_processor = externalEntityContentProcessor;
  parser->m_tagLevel = 1;
  enum XML_Error return_value_externalEntityContentProcessor=externalEntityContentProcessor(parser, start, end, endPtr);
  return return_value_externalEntityContentProcessor;
}

// externalParEntInitProcessor
// file xmlparse.c line 4279
static enum XML_Error externalParEntInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_initializeEncoding=initializeEncoding(parser);
  result = return_value_initializeEncoding;
  if(!((signed int)result == 0))
    return result;

  else
  {
    parser->m_dtd->paramEntityRead = 1;
    if(!(parser->m_prologState.inEntityValue == 0))
    {
      parser->m_processor = entityValueInitProcessor;
      enum XML_Error return_value_entityValueInitProcessor=entityValueInitProcessor(parser, s, end, nextPtr);
      return return_value_entityValueInitProcessor;
    }

    else
    {
      parser->m_processor = externalParEntProcessor;
      enum XML_Error return_value_externalParEntProcessor=externalParEntProcessor(parser, s, end, nextPtr);
      return return_value_externalParEntProcessor;
    }
  }
}

// externalParEntProcessor
// file xmlparse.c line 4383
static enum XML_Error externalParEntProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  const char *next=s;
  signed int tok=parser->m_encoding->scanners[0l](parser->m_encoding, s, end, &next);
  if(!(tok >= 1))
  {
    if(parser->m_parsingStatus.finalBuffer == 0)
    {
      if(!(tok == 0))
      {
        *nextPtr = s;
        return /*enum*/XML_ERROR_NONE;
      }

    }

    if(tok == 0)
    {
      return /*enum*/XML_ERROR_INVALID_TOKEN;
      return /*enum*/XML_ERROR_UNCLOSED_TOKEN;
      return /*enum*/XML_ERROR_PARTIAL_CHAR;
    }

  }

  else
    if(tok == 14)
    {
      XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, s, next, 4412, /*enum*/XML_ACCOUNT_DIRECT);
      if(return_value_accountingDiffTolerated == 0)
      {
        accountingOnAbort(parser);
        return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
      }

      s = next;
      tok=parser->m_encoding->scanners[0l](parser->m_encoding, s, end, &next);
    }

  parser->m_processor = prologProcessor;
  enum XML_Error return_value_doProlog=doProlog(parser, parser->m_encoding, s, end, tok, next, nextPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), 1, /*enum*/XML_ACCOUNT_DIRECT);
  return return_value_doProlog;
}

// freeBindings
// file xmlparse.c line 3211
static void freeBindings(XML_Parser parser, BINDING *bindings)
{
  while(!(bindings == ((BINDING *)NULL)))
  {
    BINDING *b=bindings;
    if(!(parser->m_endNamespaceDeclHandler == ((XML_EndNamespaceDeclHandler)NULL)))
      parser->m_endNamespaceDeclHandler(parser->m_handlerArg, b->prefix->name);

    bindings = bindings->nextTagBinding;
    b->nextTagBinding = parser->m_freeBindingList;
    parser->m_freeBindingList = b;
    b->prefix->binding = b->prevPrefixBinding;
  }
}

// generate_hash_secret_salt
// file xmlparse.c line 899
static unsigned long int generate_hash_secret_salt(XML_Parser parser)
{
  unsigned long int entropy;
  (void)parser;
  arc4random_buf(&entropy, sizeof(unsigned long int) /*8ul*/ );
  unsigned long int return_value_ENTROPY_DEBUG=ENTROPY_DEBUG("arc4random_buf", entropy);
  return return_value_ENTROPY_DEBUG;
}

// getAttributeId
// file xmlparse.c line 6324
static ATTRIBUTE_ID * getAttributeId(XML_Parser parser, const ENCODING *enc, const char *start, const char *end)
{
  DTD * const dtd=parser->m_dtd;
  ATTRIBUTE_ID *id;
  const XML_Char *name;
  __CPROVER_bool tmp_if_expr;
  XML_Bool return_value_poolGrow;
  if(dtd->pool.ptr == dtd->pool.end)
  {
    return_value_poolGrow=poolGrow(&dtd->pool);
    tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
  }

  else
    tmp_if_expr = 0;
  signed int tmp_if_expr$0;
  XML_Char *tmp_post;
  if(tmp_if_expr)
    tmp_if_expr$0 = 0;

  else
  {
    tmp_post = (&dtd->pool)->ptr;
    (&dtd->pool)->ptr = (&dtd->pool)->ptr + 1l;
    *tmp_post = 0;
    tmp_if_expr$0 = 1;
  }
  __CPROVER_bool tmp_if_expr$5;
  __CPROVER_bool tmp_if_expr$6;
  __CPROVER_bool tmp_if_expr$7;
  __CPROVER_bool tmp_if_expr$8;
  __CPROVER_bool tmp_if_expr$10;
  __CPROVER_bool tmp_if_expr$9;
  NAMED *return_value_lookup$0;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post$0;
  XML_Bool return_value_poolGrow$1;
  XML_Char *tmp_post$1;
  if(tmp_if_expr$0 == 0)
    return ((ATTRIBUTE_ID *)NULL);

  else
  {
    name=poolStoreString(&dtd->pool, enc, start, end);
    if(name == ((const XML_Char *)NULL))
      return ((ATTRIBUTE_ID *)NULL);

    else
    {
      name = name + 1l;
      NAMED *return_value_lookup=lookup(parser, &dtd->attributeIds, name, sizeof(ATTRIBUTE_ID) /*24ul*/ );
      id = (ATTRIBUTE_ID *)return_value_lookup;
      if(id == ((ATTRIBUTE_ID *)NULL))
        return ((ATTRIBUTE_ID *)NULL);

      else
      {
        if(!(id->name == name))
          (&dtd->pool)->ptr = (&dtd->pool)->start;

        else
        {
          (&dtd->pool)->start = (&dtd->pool)->ptr;
          if(!(parser->m_ns == 0))
          {
            if((signed int)*name == 0x78)
              tmp_if_expr$5 = (signed int)name[1l] == 0x6D ? 1 : 0;

            else
              tmp_if_expr$5 = 0;
            if(tmp_if_expr$5)
              tmp_if_expr$6 = (signed int)name[2l] == 0x6C ? 1 : 0;

            else
              tmp_if_expr$6 = 0;
            if(tmp_if_expr$6)
              tmp_if_expr$7 = (signed int)name[3l] == 0x6E ? 1 : 0;

            else
              tmp_if_expr$7 = 0;
            if(tmp_if_expr$7)
              tmp_if_expr$8 = (signed int)name[4l] == 0x73 ? 1 : 0;

            else
              tmp_if_expr$8 = 0;
            if(tmp_if_expr$8)
            {
              if((signed int)name[5l] == 0)
                tmp_if_expr$9 = 1;

              else
                tmp_if_expr$9 = (signed int)name[5l] == 0x3A ? 1 : 0;
              tmp_if_expr$10 = tmp_if_expr$9 ? 1 : 0;
            }

            else
              tmp_if_expr$10 = 0;
            if(tmp_if_expr$10)
            {
              if((signed int)name[5l] == 0)
                id->prefix = &dtd->defaultPrefix;

              else
              {
                return_value_lookup$0=lookup(parser, &dtd->prefixes, name + 6l, sizeof(PREFIX) /*16ul*/ );
                id->prefix = (PREFIX *)return_value_lookup$0;
              }
              id->xmlns = 1;
            }

            else
            {
              signed int i=0;
              for( ; !(name[(signed long int)i] == 0); i = i + 1)
                if((signed int)name[(signed long int)i] == 0x3A)
                {
                  signed int j=0;
                  for( ; !(j >= i); j = j + 1)
                  {
                    __CPROVER_bool tmp_if_expr$1;
                    if(dtd->pool.ptr == dtd->pool.end)
                    {
                      return_value_poolGrow$0=poolGrow(&dtd->pool);
                      tmp_if_expr$1 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
                    }

                    else
                      tmp_if_expr$1 = 0;
                    signed int tmp_if_expr$2;
                    if(tmp_if_expr$1)
                      tmp_if_expr$2 = 0;

                    else
                    {
                      tmp_post$0 = (&dtd->pool)->ptr;
                      (&dtd->pool)->ptr = (&dtd->pool)->ptr + 1l;
                      *tmp_post$0 = name[(signed long int)j];
                      tmp_if_expr$2 = 1;
                    }
                    if(tmp_if_expr$2 == 0)
                      return ((ATTRIBUTE_ID *)NULL);

                  }
                  __CPROVER_bool tmp_if_expr$3;
                  if(dtd->pool.ptr == dtd->pool.end)
                  {
                    return_value_poolGrow$1=poolGrow(&dtd->pool);
                    tmp_if_expr$3 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
                  }

                  else
                    tmp_if_expr$3 = 0;
                  signed int tmp_if_expr$4;
                  if(tmp_if_expr$3)
                    tmp_if_expr$4 = 0;

                  else
                  {
                    tmp_post$1 = (&dtd->pool)->ptr;
                    (&dtd->pool)->ptr = (&dtd->pool)->ptr + 1l;
                    *tmp_post$1 = 0;
                    tmp_if_expr$4 = 1;
                  }
                  if(tmp_if_expr$4 == 0)
                    return ((ATTRIBUTE_ID *)NULL);

                  NAMED *return_value_lookup$1=lookup(parser, &dtd->prefixes, (&dtd->pool)->start, sizeof(PREFIX) /*16ul*/ );
                  id->prefix = (PREFIX *)return_value_lookup$1;
                  if(id->prefix == ((PREFIX *)NULL))
                    return ((ATTRIBUTE_ID *)NULL);

                  if(id->prefix->name == dtd->pool.start)
                    (&dtd->pool)->start = (&dtd->pool)->ptr;

                  else
                    (&dtd->pool)->ptr = (&dtd->pool)->start;
                  break;
                }

            }
          }

        }
        return id;
      }
    }
  }
}

// getContext
// file xmlparse.c line 6387
static const XML_Char * getContext(XML_Parser parser)
{
  DTD * const dtd=parser->m_dtd;
  HASH_TABLE_ITER iter;
  XML_Bool needSep=0;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post$0;
  if(!(dtd->defaultPrefix.binding == ((BINDING *)NULL)))
  {
    signed int i;
    signed int len;
    __CPROVER_bool tmp_if_expr;
    if(parser->m_tempPool.ptr == parser->m_tempPool.end)
    {
      return_value_poolGrow=poolGrow(&parser->m_tempPool);
      tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post = (&parser->m_tempPool)->ptr;
      (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
      *tmp_post = '=';
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return ((const XML_Char *)NULL);

    len = dtd->defaultPrefix.binding->uriLen;
    if(!(parser->m_namespaceSeparator == 0))
      len = len - 1;

    i = 0;
    for( ; !(i >= len); i = i + 1)
    {
      __CPROVER_bool tmp_if_expr$1;
      if(parser->m_tempPool.ptr == parser->m_tempPool.end)
      {
        return_value_poolGrow$0=poolGrow(&parser->m_tempPool);
        tmp_if_expr$1 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
      }

      else
        tmp_if_expr$1 = 0;
      signed int tmp_if_expr$2;
      if(tmp_if_expr$1)
        tmp_if_expr$2 = 0;

      else
      {
        tmp_post$0 = (&parser->m_tempPool)->ptr;
        (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
        *tmp_post$0 = dtd->defaultPrefix.binding->uri[(signed long int)i];
        tmp_if_expr$2 = 1;
      }
      if(tmp_if_expr$2 == 0)
        return ((const XML_Char *)NULL);

    }
    needSep = 1;
  }

  hashTableIterInit(&iter, &dtd->prefixes);
  __CPROVER_bool tmp_if_expr$3;
  XML_Bool return_value_poolGrow$1;
  signed int tmp_if_expr$4;
  XML_Char *tmp_post$1;
  __CPROVER_bool tmp_if_expr$5;
  XML_Bool return_value_poolGrow$2;
  signed int tmp_if_expr$6;
  XML_Char *tmp_post$2;
  XML_Bool return_value_poolGrow$3;
  XML_Char *tmp_post$3;
  __CPROVER_bool tmp_if_expr$9;
  XML_Bool return_value_poolGrow$4;
  signed int tmp_if_expr$10;
  XML_Char *tmp_post$4;
  while(1)
  {
    signed int getContext$$1$$2$$1$$i;
    signed int getContext$$1$$2$$1$$len;
    const XML_Char *s;
    PREFIX *prefix;
    NAMED *return_value_hashTableIterNext=hashTableIterNext(&iter);
    prefix = (PREFIX *)return_value_hashTableIterNext;
    if(prefix == ((PREFIX *)NULL))
      break;

    if(!(prefix->binding == ((BINDING *)NULL)))
    {
      if(!(needSep == 0))
      {
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$1=poolGrow(&parser->m_tempPool);
          tmp_if_expr$3 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$3 = 0;
        if(tmp_if_expr$3)
          tmp_if_expr$4 = 0;

        else
        {
          tmp_post$1 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$1 = 12;
          tmp_if_expr$4 = 1;
        }
        if(tmp_if_expr$4 == 0)
          return ((const XML_Char *)NULL);

      }

      s = prefix->name;
      for( ; !(*s == 0); s = s + 1l)
      {
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$2=poolGrow(&parser->m_tempPool);
          tmp_if_expr$5 = !(return_value_poolGrow$2 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$5 = 0;
        if(tmp_if_expr$5)
          tmp_if_expr$6 = 0;

        else
        {
          tmp_post$2 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$2 = *s;
          tmp_if_expr$6 = 1;
        }
        if(tmp_if_expr$6 == 0)
          return ((const XML_Char *)NULL);

      }
      __CPROVER_bool tmp_if_expr$7;
      if(parser->m_tempPool.ptr == parser->m_tempPool.end)
      {
        return_value_poolGrow$3=poolGrow(&parser->m_tempPool);
        tmp_if_expr$7 = !(return_value_poolGrow$3 != 0) ? 1 : 0;
      }

      else
        tmp_if_expr$7 = 0;
      signed int tmp_if_expr$8;
      if(tmp_if_expr$7)
        tmp_if_expr$8 = 0;

      else
      {
        tmp_post$3 = (&parser->m_tempPool)->ptr;
        (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
        *tmp_post$3 = '=';
        tmp_if_expr$8 = 1;
      }
      if(tmp_if_expr$8 == 0)
        return ((const XML_Char *)NULL);

      getContext$$1$$2$$1$$len = prefix->binding->uriLen;
      if(!(parser->m_namespaceSeparator == 0))
        getContext$$1$$2$$1$$len = getContext$$1$$2$$1$$len - 1;

      getContext$$1$$2$$1$$i = 0;
      for( ; !(getContext$$1$$2$$1$$i >= getContext$$1$$2$$1$$len); getContext$$1$$2$$1$$i = getContext$$1$$2$$1$$i + 1)
      {
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$4=poolGrow(&parser->m_tempPool);
          tmp_if_expr$9 = !(return_value_poolGrow$4 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$9 = 0;
        if(tmp_if_expr$9)
          tmp_if_expr$10 = 0;

        else
        {
          tmp_post$4 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$4 = prefix->binding->uri[(signed long int)getContext$$1$$2$$1$$i];
          tmp_if_expr$10 = 1;
        }
        if(tmp_if_expr$10 == 0)
          return ((const XML_Char *)NULL);

      }
      needSep = 1;
    }

  }
  hashTableIterInit(&iter, &dtd->generalEntities);
  __CPROVER_bool tmp_if_expr$11;
  XML_Bool return_value_poolGrow$5;
  signed int tmp_if_expr$12;
  XML_Char *tmp_post$5;
  __CPROVER_bool tmp_if_expr$13;
  XML_Bool return_value_poolGrow$6;
  signed int tmp_if_expr$14;
  XML_Char *tmp_post$6;
  while(1)
  {
    const XML_Char *getContext$$1$$3$$1$$s;
    ENTITY *e;
    NAMED *return_value_hashTableIterNext$0=hashTableIterNext(&iter);
    e = (ENTITY *)return_value_hashTableIterNext$0;
    if(e == ((ENTITY *)NULL))
      break;

    if(!(e->open == 0))
    {
      if(!(needSep == 0))
      {
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$5=poolGrow(&parser->m_tempPool);
          tmp_if_expr$11 = !(return_value_poolGrow$5 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$11 = 0;
        if(tmp_if_expr$11)
          tmp_if_expr$12 = 0;

        else
        {
          tmp_post$5 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$5 = 12;
          tmp_if_expr$12 = 1;
        }
        if(tmp_if_expr$12 == 0)
          return ((const XML_Char *)NULL);

      }

      getContext$$1$$3$$1$$s = e->name;
      for( ; !(*getContext$$1$$3$$1$$s == 0); getContext$$1$$3$$1$$s = getContext$$1$$3$$1$$s + 1l)
      {
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$6=poolGrow(&parser->m_tempPool);
          tmp_if_expr$13 = !(return_value_poolGrow$6 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$13 = 0;
        if(tmp_if_expr$13)
          tmp_if_expr$14 = 0;

        else
        {
          tmp_post$6 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$6 = *getContext$$1$$3$$1$$s;
          tmp_if_expr$14 = 1;
        }
        if(tmp_if_expr$14 == 0)
          return ((const XML_Char *)NULL);

      }
      needSep = 1;
    }

  }
  __CPROVER_bool tmp_if_expr$15;
  XML_Bool return_value_poolGrow$7;
  if(parser->m_tempPool.ptr == parser->m_tempPool.end)
  {
    return_value_poolGrow$7=poolGrow(&parser->m_tempPool);
    tmp_if_expr$15 = !(return_value_poolGrow$7 != 0) ? 1 : 0;
  }

  else
    tmp_if_expr$15 = 0;
  signed int tmp_if_expr$16;
  XML_Char *tmp_post$7;
  if(tmp_if_expr$15)
    tmp_if_expr$16 = 0;

  else
  {
    tmp_post$7 = (&parser->m_tempPool)->ptr;
    (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
    *tmp_post$7 = 0;
    tmp_if_expr$16 = 1;
  }
  if(tmp_if_expr$16 == 0)
    return ((const XML_Char *)NULL);

  else
    return parser->m_tempPool.start;
}

// getDebugLevel
// file xmlparse.c line 8224
static unsigned long int getDebugLevel(const char *variableName, unsigned long int defaultDebugLevel)
{
  const char *valueOrNull;
  char *return_value_getenv=getenv(variableName);
  valueOrNull = return_value_getenv;
  if(valueOrNull == ((const char *)NULL))
    return defaultDebugLevel;

  else
  {
    const char * const value=valueOrNull;
    signed int *return_value___errno_location=__errno_location();
    *return_value___errno_location = 0;
    char *afterValue=(char *)value;
    unsigned long int debugLevel;
    unsigned long int return_value_strtoul=strtoul(value, &afterValue, 10);
    debugLevel = return_value_strtoul;
    signed int *return_value___errno_location$1=__errno_location();
    __CPROVER_bool tmp_if_expr;
    if(!(*return_value___errno_location$1 == 0))
      tmp_if_expr = 1;

    else
      tmp_if_expr = (signed int)afterValue[0l] != 0 ? 1 : 0;
    if(tmp_if_expr)
    {
      signed int *return_value___errno_location$0=__errno_location();
      *return_value___errno_location$0 = 0;
      return defaultDebugLevel;
    }

    else
      return debugLevel;
  }
}

// getElementType
// file xmlparse.c line 7447
static ELEMENT_TYPE * getElementType(XML_Parser parser, const ENCODING *enc, const char *ptr, const char *end)
{
  DTD * const dtd=parser->m_dtd;
  const XML_Char *name;
  XML_Char *return_value_poolStoreString=poolStoreString(&dtd->pool, enc, ptr, end);
  name = return_value_poolStoreString;
  ELEMENT_TYPE *ret;
  if(name == ((const XML_Char *)NULL))
    return ((ELEMENT_TYPE *)NULL);

  else
  {
    NAMED *return_value_lookup=lookup(parser, &dtd->elementTypes, name, sizeof(ELEMENT_TYPE) /*40ul*/ );
    ret = (ELEMENT_TYPE *)return_value_lookup;
    if(ret == ((ELEMENT_TYPE *)NULL))
      return ((ELEMENT_TYPE *)NULL);

    else
    {
      if(!(ret->name == name))
        (&dtd->pool)->ptr = (&dtd->pool)->start;

      else
      {
        (&dtd->pool)->start = (&dtd->pool)->ptr;
        signed int return_value_setElementTypePrefix=setElementTypePrefix(parser, ret);
        if(return_value_setElementTypePrefix == 0)
          return ((ELEMENT_TYPE *)NULL);

      }
      return ret;
    }
  }
}

// getRootParserOf
// file xmlparse.c line 7685
static XML_Parser getRootParserOf(XML_Parser parser, unsigned int *outLevelDiff)
{
  XML_Parser rootParser=parser;
  unsigned int stepsTakenUpwards=0u;
  for( ; !(rootParser->m_parentParser == ((XML_Parser)NULL)); stepsTakenUpwards = stepsTakenUpwards + 1u)
    rootParser = rootParser->m_parentParser;
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion ! rootParser->m_parentParser */
  assert(!(rootParser->m_parentParser != ((XML_Parser)NULL)));
  if(!(outLevelDiff == ((unsigned int *)NULL)))
    *outLevelDiff = stepsTakenUpwards;

  return rootParser;
}

// get_hash_secret_salt
// file xmlparse.c line 942
static unsigned long int get_hash_secret_salt(XML_Parser parser)
{
  unsigned long int return_value_get_hash_secret_salt;
  if(!(parser->m_parentParser == ((XML_Parser)NULL)))
  {
    return_value_get_hash_secret_salt=get_hash_secret_salt(parser->m_parentParser);
    return return_value_get_hash_secret_salt;
  }

  else
    return parser->m_hash_secret_salt;
}

// handleUnknownEncoding
// file xmlparse.c line 4233
static enum XML_Error handleUnknownEncoding(XML_Parser parser, const XML_Char *encodingName)
{
  if(!(parser->m_unknownEncodingHandler == ((XML_UnknownEncodingHandler)NULL)))
  {
    XML_Encoding info;
    signed int i=0;
    for( ; !(i >= 256); i = i + 1)
      info.map[(signed long int)i] = -1;
    info.convert = ((signed int (*)(void *, const char *))NULL);
    info.data = NULL;
    info.release = ((void (*)(void *))NULL);
    signed int return_value$0=parser->m_unknownEncodingHandler(parser->m_unknownEncodingHandlerData, encodingName, &info);
    if(!(return_value$0 == 0))
    {
      ENCODING *enc;
      void *return_value;
      signed int return_value_XmlSizeOfUnknownEncoding=XmlSizeOfUnknownEncoding();
      return_value=parser->m_mem.malloc_fcn((size_t)return_value_XmlSizeOfUnknownEncoding);
      parser->m_unknownEncodingMem = return_value;
      if(parser->m_unknownEncodingMem == NULL)
      {
        if(!(info.release == ((void (*)(void *))NULL)))
          info.release(info.data);

        return /*enum*/XML_ERROR_NO_MEMORY;
      }

      enc=(parser->m_ns != 0 ? XmlInitUnknownEncodingNS : XmlInitUnknownEncoding)(parser->m_unknownEncodingMem, info.map, info.convert, info.data);
      if(!(enc == ((ENCODING *)NULL)))
      {
        parser->m_unknownEncodingData = info.data;
        parser->m_unknownEncodingRelease = info.release;
        parser->m_encoding = enc;
        return /*enum*/XML_ERROR_NONE;
      }

    }

    if(!(info.release == ((void (*)(void *))NULL)))
      info.release(info.data);

  }

  return /*enum*/XML_ERROR_UNKNOWN_ENCODING;
}

// hash
// file xmlparse.c line 6880
static unsigned long int hash(XML_Parser parser, KEY s)
{
  struct siphash state;
  struct sipkey key;
  (void)sip24_valid;
  copy_salt_to_sipkey(parser, &key);
  sip24_init(&state, &key);
  size_t return_value_keylen=keylen(s);
  sip24_update(&state, (const void *)s, return_value_keylen * sizeof(XML_Char) /*1ul*/ );
  uint64_t return_value_sip24_final=sip24_final(&state);
  return (unsigned long int)return_value_sip24_final;
}

// hashTableClear
// file xmlparse.c line 6980
static void hashTableClear(HASH_TABLE *table)
{
  size_t i=0ul;
  if(!(i >= table->size))
  {
    table->mem->free_fcn((void *)table->v[(signed long int)i]);
    table->v[(signed long int)i] = ((NAMED *)NULL);
    i = i + 1ul;
  }

  table->used = 0ul;
}

// hashTableDestroy
// file xmlparse.c line 6990
static void hashTableDestroy(HASH_TABLE *table)
{
  size_t i=0ul;
  if(!(i >= table->size))
  {
    table->mem->free_fcn((void *)table->v[(signed long int)i]);
    i = i + 1ul;
  }

  table->mem->free_fcn((void *)table->v);
}

// hashTableInit
// file xmlparse.c line 6998
static void hashTableInit(HASH_TABLE *p, const XML_Memory_Handling_Suite *ms)
{
  p->power = 0;
  p->size = 0ul;
  p->used = 0ul;
  p->v = ((NAMED **)NULL);
  p->mem = ms;
}

// hashTableIterInit
// file xmlparse.c line 7007
static void hashTableIterInit(HASH_TABLE_ITER *iter, const HASH_TABLE *table)
{
  iter->p = table->v;
  NAMED **tmp_if_expr;
  if(!(iter->p == ((NAMED **)NULL)))
    tmp_if_expr = iter->p + (signed long int)table->size;

  else
    tmp_if_expr = ((NAMED **)NULL);
  iter->end = tmp_if_expr;
}

// hashTableIterNext
// file xmlparse.c line 7013
static NAMED * hashTableIterNext(HASH_TABLE_ITER *iter)
{
  while(!(iter->p == iter->end))
  {
    NAMED *tem;
    NAMED **tmp_post=iter->p;
    iter->p = iter->p + 1l;
    tem = *tmp_post;
    if(!(tem == ((NAMED *)NULL)))
      return tem;

  }
  return ((NAMED *)NULL);
}

// ignoreSectionProcessor
// file xmlparse.c line 4011
static enum XML_Error ignoreSectionProcessor(XML_Parser parser, const char *start, const char *end, const char **endPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_doIgnoreSection=doIgnoreSection(parser, parser->m_encoding, &start, end, endPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0));
  result = return_value_doIgnoreSection;
  if(!((signed int)result == 0))
    return result;

  else
    if(!(start == ((const char *)NULL)))
    {
      parser->m_processor = prologProcessor;
      enum XML_Error return_value_prologProcessor=prologProcessor(parser, start, end, endPtr);
      return return_value_prologProcessor;
    }

    else
      return result;
}

// initializeEncoding
// file xmlparse.c line 4111
static enum XML_Error initializeEncoding(XML_Parser parser)
{
  const char *s=parser->m_protocolEncodingName;
  signed int return_value=(parser->m_ns != 0 ? XmlInitEncodingNS : XmlInitEncoding)(&parser->m_initEncoding, &parser->m_encoding, s);
  if(!(return_value == 0))
    return /*enum*/XML_ERROR_NONE;

  else
  {
    enum XML_Error return_value_handleUnknownEncoding=handleUnknownEncoding(parser, parser->m_protocolEncodingName);
    return return_value_handleUnknownEncoding;
  }
}

// internalEntityProcessor
// file xmlparse.c line 5643
static enum XML_Error internalEntityProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  ENTITY *entity;
  const char *textStart;
  const char *textEnd;
  const char *next;
  enum XML_Error result;
  OPEN_INTERNAL_ENTITY *openEntity=parser->m_openInternalEntities;
  __CPROVER_bool tmp_if_expr;
  if(openEntity == ((OPEN_INTERNAL_ENTITY *)NULL))
    return /*enum*/XML_ERROR_UNEXPECTED_STATE;

  else
  {
    entity = openEntity->entity;
    textStart = (const char *)entity->textPtr + (signed long int)entity->processed;
    textEnd = (const char *)(entity->textPtr + (signed long int)entity->textLen);
    next = textStart;
    if(!(entity->is_param == 0))
    {
      signed int tok;
      signed int return_value=parser->m_internalEncoding->scanners[0l](parser->m_internalEncoding, textStart, textEnd, &next);
      tok = return_value;
      result=doProlog(parser, parser->m_internalEncoding, textStart, textEnd, tok, next, &next, 0, 1, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
    }

    else
      result=doContent(parser, openEntity->startTagLevel, parser->m_internalEncoding, textStart, textEnd, &next, 0, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
    if(!((signed int)result == 0))
      return result;

    else
    {
      if(!(textEnd == next))
        tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;

      else
        tmp_if_expr = 0;
      if(tmp_if_expr)
      {
        entity->processed = (signed int)(next - (const char *)entity->textPtr);
        return result;
      }

      else
      {
        entityTrackingOnClose(parser, entity, 5680);
        entity->open = 0;
        parser->m_openInternalEntities = openEntity->next;
        openEntity->next = parser->m_freeInternalEntities;
        parser->m_freeInternalEntities = openEntity;
      }
    }
    if(!(entity->is_param == 0))
    {
      signed int internalEntityProcessor$$1$$4$$tok;
      parser->m_processor = prologProcessor;
      internalEntityProcessor$$1$$4$$tok=parser->m_encoding->scanners[0l](parser->m_encoding, s, end, &next);
      enum XML_Error return_value_doProlog=doProlog(parser, parser->m_encoding, s, end, internalEntityProcessor$$1$$4$$tok, next, nextPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), 1, /*enum*/XML_ACCOUNT_DIRECT);
      return return_value_doProlog;
    }

    else
    {
      parser->m_processor = contentProcessor;
      enum XML_Error return_value_doContent=doContent(parser, parser->m_parentParser != ((XML_Parser)NULL) ? 1 : 0, parser->m_encoding, s, end, nextPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), /*enum*/XML_ACCOUNT_DIRECT);
      return return_value_doContent;
    }
  }
}

// keyeq
// file xmlparse.c line 6858
static XML_Bool keyeq(KEY s1, KEY s2)
{
  for( ; *s1 == *s2; s2 = s2 + 1l)
  {
    if((signed int)*s1 == 0)
      return 1;

    s1 = s1 + 1l;
  }
  return 0;
}

// keylen
// file xmlparse.c line 6866
static size_t keylen(KEY s)
{
  size_t len=0ul;
  for( ; !(*s == 0); len = len + 1ul)
    s = s + 1l;
  return len;
}

// lookup
// file xmlparse.c line 6891
static NAMED * lookup(XML_Parser parser, HASH_TABLE *table, KEY name, size_t createSize)
{
  size_t i;
  if(table->size == 0ul)
  {
    size_t lookup$$1$$1$$tsize;
    if(createSize == 0ul)
      return ((NAMED *)NULL);

    table->power = 6;
    table->size = 1ul << 6;
    lookup$$1$$1$$tsize = table->size * sizeof(NAMED *) /*8ul*/ ;
    void *return_value=table->mem->malloc_fcn(lookup$$1$$1$$tsize);
    table->v = (NAMED **)return_value;
    if(table->v == ((NAMED **)NULL))
    {
      table->size = 0ul;
      return ((NAMED *)NULL);
    }

    memset((void *)table->v, 0, lookup$$1$$1$$tsize);
    unsigned long int return_value_hash=hash(parser, name);
    i = return_value_hash & (unsigned long int)table->size - 1ul;
  }

  else
  {
    unsigned long int h;
    unsigned long int return_value_hash$0=hash(parser, name);
    h = return_value_hash$0;
    unsigned long int mask=(unsigned long int)table->size - 1ul;
    unsigned char step=0;
    i = h & mask;
    while(!(table->v[(signed long int)i] == ((NAMED *)NULL)))
    {
      XML_Bool return_value_keyeq=keyeq(name, table->v[(signed long int)i]->name);
      if(!(return_value_keyeq == 0))
        return table->v[(signed long int)i];

      if(step == 0)
        step = (unsigned char)((h & ~mask) >> (signed int)table->power - 1 & mask >> 2 | 1ul);

      if(!(i >= (unsigned long int)step))
        i = i + (table->size - (unsigned long int)step);

      else
        i = i - (unsigned long int)step;
    }
    if(createSize == 0ul)
      return ((NAMED *)NULL);

    if(!(table->used >> (signed int)table->power + -1 == 0ul))
    {
      unsigned char newPower=(unsigned char)((signed int)table->power + 1);
      if((unsigned long int)newPower >= sizeof(unsigned long int) * 8ul /*64ul*/ )
        return ((NAMED *)NULL);

      size_t newSize=1ul << (signed int)newPower;
      unsigned long int newMask=(unsigned long int)newSize - 1ul;
      if(newSize >= 2305843009213693952ul)
        return ((NAMED *)NULL);

      size_t tsize=newSize * sizeof(NAMED *) /*8ul*/ ;
      NAMED **newV;
      void *return_value$0=table->mem->malloc_fcn(tsize);
      newV = (NAMED **)return_value$0;
      if(newV == ((NAMED **)NULL))
        return ((NAMED *)NULL);

      memset((void *)newV, 0, tsize);
      i = 0ul;
      if(!(i >= table->size))
      {
        if(!(table->v[(signed long int)i] == ((NAMED *)NULL)))
        {
          unsigned long int newHash;
          unsigned long int return_value_hash$1=hash(parser, table->v[(signed long int)i]->name);
          newHash = return_value_hash$1;
          size_t j=newHash & newMask;
          step = 0;
          if(!(newV[(signed long int)j] == ((NAMED *)NULL)))
          {
            if(step == 0)
              step = (unsigned char)((newHash & ~newMask) >> (signed int)newPower - 1 & newMask >> 2 | 1ul);

            if(!(j >= (unsigned long int)step))
              j = j + (newSize - (unsigned long int)step);

            else
              j = j - (unsigned long int)step;
          }

          newV[(signed long int)j] = table->v[(signed long int)i];
        }

        i = i + 1ul;
      }

      table->mem->free_fcn((void *)table->v);
      table->v = newV;
      table->power = newPower;
      table->size = newSize;
      i = h & newMask;
      step = 0;
      if(!(table->v[(signed long int)i] == ((NAMED *)NULL)))
      {
        if(step == 0)
          step = (unsigned char)((h & ~newMask) >> (signed int)newPower - 1 & newMask >> 2 | 1ul);

        if(!(i >= (unsigned long int)step))
          i = i + (newSize - (unsigned long int)step);

        else
          i = i - (unsigned long int)step;
      }

    }

  }
  void *return_value$1=table->mem->malloc_fcn(createSize);
  table->v[(signed long int)i] = (NAMED *)return_value$1;
  if(table->v[(signed long int)i] == ((NAMED *)NULL))
    return ((NAMED *)NULL);

  else
  {
    memset((void *)table->v[(signed long int)i], 0, createSize);
    table->v[(signed long int)i]->name = name;
    table->used = table->used + 1ul;
    return table->v[(signed long int)i];
  }
}

// moveToFreeBindingList
// file xmlparse.c line 1170
static void moveToFreeBindingList(XML_Parser parser, BINDING *bindings)
{
  while(!(bindings == ((BINDING *)NULL)))
  {
    BINDING *b=bindings;
    bindings = bindings->nextTagBinding;
    b->nextTagBinding = parser->m_freeBindingList;
    parser->m_freeBindingList = b;
  }
}

// nextScaffoldPart
// file xmlparse.c line 7274
static signed int nextScaffoldPart(XML_Parser parser)
{
  DTD * const dtd=parser->m_dtd;
  CONTENT_SCAFFOLD *me;
  signed int next;
  if(dtd->scaffIndex == ((signed int *)NULL))
  {
    void *return_value=parser->m_mem.malloc_fcn((unsigned long int)parser->m_groupSize * sizeof(signed int) /*4ul*/ );
    dtd->scaffIndex = (signed int *)return_value;
    if(dtd->scaffIndex == ((signed int *)NULL))
      return -1;

    dtd->scaffIndex[0l] = 0;
  }

  if(dtd->scaffCount >= dtd->scaffSize)
  {
    CONTENT_SCAFFOLD *temp;
    if(!(dtd->scaffold == ((CONTENT_SCAFFOLD *)NULL)))
    {
      if(dtd->scaffSize >= 2147483648u)
        return -1;

      void *return_value$0=parser->m_mem.realloc_fcn((void *)dtd->scaffold, (unsigned long int)(dtd->scaffSize * 2u) * sizeof(CONTENT_SCAFFOLD) /*32ul*/ );
      temp = (CONTENT_SCAFFOLD *)return_value$0;
      if(temp == ((CONTENT_SCAFFOLD *)NULL))
        return -1;

      dtd->scaffSize = dtd->scaffSize * 2u;
    }

    else
    {
      void *return_value$1=parser->m_mem.malloc_fcn(32ul * sizeof(CONTENT_SCAFFOLD) /*32ul*/ );
      temp = (CONTENT_SCAFFOLD *)return_value$1;
      if(temp == ((CONTENT_SCAFFOLD *)NULL))
        return -1;

      dtd->scaffSize = 32u;
    }
    dtd->scaffold = temp;
  }

  unsigned int tmp_post=dtd->scaffCount;
  dtd->scaffCount = dtd->scaffCount + 1u;
  next = (signed int)tmp_post;
  me = &dtd->scaffold[(signed long int)next];
  if(!(dtd->scaffLevel == 0))
  {
    CONTENT_SCAFFOLD *parent=&dtd->scaffold[(signed long int)dtd->scaffIndex[(signed long int)(dtd->scaffLevel - 1)]];
    if(!(parent->lastchild == 0))
      (dtd->scaffold + (signed long int)parent->lastchild)->nextsib = next;

    if(parent->childcnt == 0)
      parent->firstchild = next;

    parent->lastchild = next;
    parent->childcnt = parent->childcnt + 1;
  }

  me->nextsib = 0;
  me->childcnt = 0;
  me->lastchild = 0;
  me->firstchild = 0;
  return next;
}

// normalizeLines
// file xmlparse.c line 6120
static void normalizeLines(XML_Char *s)
{
  XML_Char *p;
  for( ; 1; s = s + 1l)
  {
    if((signed int)*s == 0)
      goto __CPROVER_DUMP_L8;

    if((signed int)*s == 0xD)
      break;

  }
  p = s;
  XML_Char *tmp_post$0;
  XML_Char *tmp_post$1;
  while(1)
  {
    if((signed int)*s == 0xD)
    {
      XML_Char *tmp_post=p;
      p = p + 1l;
      *tmp_post = '\n';
      s = s + 1l;
      if((signed int)*s == 0xA)
        s = s + 1l;

    }

    else
    {
      tmp_post$0 = p;
      p = p + 1l;
      tmp_post$1 = s;
      s = s + 1l;
      *tmp_post$0 = *tmp_post$1;
    }
    if(*s == 0)
      break;

  }
  *p = 0;

__CPROVER_DUMP_L8:
  ;
}

// normalizePublicId
// file xmlparse.c line 6543
static void normalizePublicId(XML_Char *publicId)
{
  XML_Char *p=publicId;
  XML_Char *s=publicId;
  XML_Char *tmp_post;
  for( ; !(*s == 0); s = s + 1l)
  {
    signed int tmp_switch_value=(signed int)*s;
    if(tmp_switch_value == 0xA || tmp_switch_value == 0xD || tmp_switch_value == 0x20)
    {
      if(!(p == publicId))
      {
        if(!((signed int)p[-1l] == 0x20))
        {
          tmp_post = p;
          p = p + 1l;
          *tmp_post = ' ';
        }

      }

    }

    else
    {
      XML_Char *tmp_post$0=p;
      p = p + 1l;
      *tmp_post$0 = *s;
    }
  }
  if(!(p == publicId))
  {
    if((signed int)p[-1l] == 0x20)
      p = p - 1l;

  }

  *p = 0;
}

// parserCreate
// file xmlparse.c line 970
static XML_Parser parserCreate(const XML_Char *encodingName, const XML_Memory_Handling_Suite *memsuite, const XML_Char *nameSep, DTD *dtd)
{
  XML_Parser parser;
  if(!(memsuite == ((const XML_Memory_Handling_Suite *)NULL)))
  {
    XML_Memory_Handling_Suite *mtemp;
    void *return_value=memsuite->malloc_fcn(sizeof(struct XML_ParserStruct) /*976ul*/ );
    parser = (XML_Parser)return_value;
    if(!(parser == ((XML_Parser)NULL)))
    {
      mtemp = (XML_Memory_Handling_Suite *)&parser->m_mem;
      mtemp->malloc_fcn = memsuite->malloc_fcn;
      mtemp->realloc_fcn = memsuite->realloc_fcn;
      mtemp->free_fcn = memsuite->free_fcn;
    }

  }

  else
  {
    XML_Memory_Handling_Suite *parserCreate$$1$$2$$mtemp;
    void *return_value_malloc=malloc(sizeof(struct XML_ParserStruct) /*976ul*/ );
    parser = (XML_Parser)return_value_malloc;
    if(!(parser == ((XML_Parser)NULL)))
    {
      parserCreate$$1$$2$$mtemp = (XML_Memory_Handling_Suite *)&parser->m_mem;
      parserCreate$$1$$2$$mtemp->malloc_fcn = malloc;
      parserCreate$$1$$2$$mtemp->realloc_fcn = realloc;
      parserCreate$$1$$2$$mtemp->free_fcn = free;
    }

  }
  if(parser == ((XML_Parser)NULL))
    return parser;

  else
  {
    parser->m_buffer = ((char *)NULL);
    parser->m_bufferLim = ((const char *)NULL);
    parser->m_attsSize = 16;
    void *return_value$0=parser->m_mem.malloc_fcn((unsigned long int)parser->m_attsSize * sizeof(ATTRIBUTE) /*32ul*/ );
    parser->m_atts = (ATTRIBUTE *)return_value$0;
    if(parser->m_atts == ((ATTRIBUTE *)NULL))
    {
      parser->m_mem.free_fcn((void *)parser);
      return ((XML_Parser)NULL);
    }

    else
    {
      void *return_value$1=parser->m_mem.malloc_fcn(1024ul * sizeof(XML_Char) /*1ul*/ );
      parser->m_dataBuf = (XML_Char *)return_value$1;
      if(parser->m_dataBuf == ((XML_Char *)NULL))
      {
        parser->m_mem.free_fcn((void *)parser->m_atts);
        parser->m_mem.free_fcn((void *)parser);
        return ((XML_Parser)NULL);
      }

      else
      {
        parser->m_dataBufEnd = parser->m_dataBuf + 1024l;
        if(!(dtd == ((DTD *)NULL)))
          parser->m_dtd = dtd;

        else
        {
          DTD *return_value_dtdCreate=dtdCreate(&parser->m_mem);
          parser->m_dtd = return_value_dtdCreate;
          if(parser->m_dtd == ((DTD *)NULL))
          {
            parser->m_mem.free_fcn((void *)parser->m_dataBuf);
            parser->m_mem.free_fcn((void *)parser->m_atts);
            parser->m_mem.free_fcn((void *)parser);
            return ((XML_Parser)NULL);
          }

        }
        parser->m_freeBindingList = ((BINDING *)NULL);
        parser->m_freeTagList = ((TAG *)NULL);
        parser->m_freeInternalEntities = ((OPEN_INTERNAL_ENTITY *)NULL);
        parser->m_groupSize = 0u;
        parser->m_groupConnector = ((char *)NULL);
        parser->m_unknownEncodingHandler = ((XML_UnknownEncodingHandler)NULL);
        parser->m_unknownEncodingHandlerData = NULL;
        parser->m_namespaceSeparator = '!';
        parser->m_ns = 0;
        parser->m_ns_triplets = 0;
        parser->m_nsAtts = ((NS_ATT *)NULL);
        parser->m_nsAttsVersion = 0ul;
        parser->m_nsAttsPower = 0;
        parser->m_protocolEncodingName = ((const XML_Char *)NULL);
        poolInit(&parser->m_tempPool, &parser->m_mem);
        poolInit(&parser->m_temp2Pool, &parser->m_mem);
        parserInit(parser, encodingName);
        if(!(encodingName == ((const XML_Char *)NULL)))
        {
          if(parser->m_protocolEncodingName == ((const XML_Char *)NULL))
          {
            XML_ParserFree(parser);
            return ((XML_Parser)NULL);
          }

        }

        if(!(nameSep == ((const XML_Char *)NULL)))
        {
          parser->m_ns = 1;
          const ENCODING *return_value_XmlGetUtf8InternalEncodingNS=XmlGetUtf8InternalEncodingNS();
          parser->m_internalEncoding = return_value_XmlGetUtf8InternalEncodingNS;
          parser->m_namespaceSeparator = *nameSep;
        }

        else
        {
          const ENCODING *return_value_XmlGetUtf8InternalEncoding=XmlGetUtf8InternalEncoding();
          parser->m_internalEncoding = return_value_XmlGetUtf8InternalEncoding;
        }
        return parser;
      }
    }
  }
}

// parserInit
// file xmlparse.c line 1085
static void parserInit(XML_Parser parser, const XML_Char *encodingName)
{
  parser->m_processor = prologInitProcessor;
  XmlPrologStateInit(&parser->m_prologState);
  if(!(encodingName == ((const XML_Char *)NULL)))
  {
    XML_Char *return_value_copyString=copyString(encodingName, &parser->m_mem);
    parser->m_protocolEncodingName = return_value_copyString;
  }

  parser->m_curBase = ((const XML_Char *)NULL);
  XmlInitEncoding(&parser->m_initEncoding, &parser->m_encoding, ((const char *)NULL));
  parser->m_userData = NULL;
  parser->m_handlerArg = NULL;
  parser->m_startElementHandler = ((XML_StartElementHandler)NULL);
  parser->m_endElementHandler = ((XML_EndElementHandler)NULL);
  parser->m_characterDataHandler = ((XML_CharacterDataHandler)NULL);
  parser->m_processingInstructionHandler = ((XML_ProcessingInstructionHandler)NULL);
  parser->m_commentHandler = ((XML_CommentHandler)NULL);
  parser->m_startCdataSectionHandler = ((XML_StartCdataSectionHandler)NULL);
  parser->m_endCdataSectionHandler = ((XML_EndCdataSectionHandler)NULL);
  parser->m_defaultHandler = ((XML_DefaultHandler)NULL);
  parser->m_startDoctypeDeclHandler = ((XML_StartDoctypeDeclHandler)NULL);
  parser->m_endDoctypeDeclHandler = ((XML_EndDoctypeDeclHandler)NULL);
  parser->m_unparsedEntityDeclHandler = ((XML_UnparsedEntityDeclHandler)NULL);
  parser->m_notationDeclHandler = ((XML_NotationDeclHandler)NULL);
  parser->m_startNamespaceDeclHandler = ((XML_StartNamespaceDeclHandler)NULL);
  parser->m_endNamespaceDeclHandler = ((XML_EndNamespaceDeclHandler)NULL);
  parser->m_notStandaloneHandler = ((XML_NotStandaloneHandler)NULL);
  parser->m_externalEntityRefHandler = ((XML_ExternalEntityRefHandler)NULL);
  parser->m_externalEntityRefHandlerArg = parser;
  parser->m_skippedEntityHandler = ((XML_SkippedEntityHandler)NULL);
  parser->m_elementDeclHandler = ((XML_ElementDeclHandler)NULL);
  parser->m_attlistDeclHandler = ((XML_AttlistDeclHandler)NULL);
  parser->m_entityDeclHandler = ((XML_EntityDeclHandler)NULL);
  parser->m_xmlDeclHandler = ((XML_XmlDeclHandler)NULL);
  parser->m_bufferPtr = parser->m_buffer;
  parser->m_bufferEnd = parser->m_buffer;
  parser->m_parseEndByteIndex = 0l;
  parser->m_parseEndPtr = ((const char *)NULL);
  parser->m_declElementType = ((ELEMENT_TYPE *)NULL);
  parser->m_declAttributeId = ((ATTRIBUTE_ID *)NULL);
  parser->m_declEntity = ((ENTITY *)NULL);
  parser->m_doctypeName = ((const XML_Char *)NULL);
  parser->m_doctypeSysid = ((const XML_Char *)NULL);
  parser->m_doctypePubid = ((const XML_Char *)NULL);
  parser->m_declAttributeType = ((const XML_Char *)NULL);
  parser->m_declNotationName = ((const XML_Char *)NULL);
  parser->m_declNotationPublicId = ((const XML_Char *)NULL);
  parser->m_declAttributeIsCdata = 0;
  parser->m_declAttributeIsId = 0;
  memset((void *)&parser->m_position, 0, sizeof(POSITION) /*16ul*/ );
  parser->m_errorCode = /*enum*/XML_ERROR_NONE;
  parser->m_eventPtr = ((const char *)NULL);
  parser->m_eventEndPtr = ((const char *)NULL);
  parser->m_positionPtr = ((const char *)NULL);
  parser->m_openInternalEntities = ((OPEN_INTERNAL_ENTITY *)NULL);
  parser->m_defaultExpandInternalEntities = 1;
  parser->m_tagLevel = 0;
  parser->m_tagStack = ((TAG *)NULL);
  parser->m_inheritedBindings = ((BINDING *)NULL);
  parser->m_nSpecifiedAtts = 0;
  parser->m_unknownEncodingMem = NULL;
  parser->m_unknownEncodingRelease = ((void (*)(void *))NULL);
  parser->m_unknownEncodingData = NULL;
  parser->m_parentParser = ((XML_Parser)NULL);
  parser->m_parsingStatus.parsing = /*enum*/XML_INITIALIZED;
  parser->m_isParamEntity = 0;
  parser->m_useForeignDTD = 0;
  parser->m_paramEntityParsing = /*enum*/XML_PARAM_ENTITY_PARSING_NEVER;
  parser->m_hash_secret_salt = 0ul;
  memset((void *)&parser->m_accounting, 0, sizeof(ACCOUNTING) /*32ul*/ );
  unsigned long int return_value_getDebugLevel=getDebugLevel("EXPAT_ACCOUNTING_DEBUG", 0ul);
  parser->m_accounting.debugLevel = (signed int)return_value_getDebugLevel;
  parser->m_accounting.maximumAmplificationFactor = 100.0f;
  parser->m_accounting.activationThresholdBytes = 8388608ull;
  memset((void *)&parser->m_entity_stats, 0, sizeof(ENTITY_STATS) /*16ul*/ );
  unsigned long int return_value_getDebugLevel$0=getDebugLevel("EXPAT_ENTITY_DEBUG", 0ul);
  parser->m_entity_stats.debugLevel = (signed int)return_value_getDebugLevel$0;
}

// poolAppend
// file xmlparse.c line 7068
static XML_Char * poolAppend(STRING_POOL *pool, const ENCODING *enc, const char *ptr, const char *end)
{
  XML_Bool return_value_poolGrow;
  if(pool->ptr == ((XML_Char *)NULL))
  {
    return_value_poolGrow=poolGrow(pool);
    if(return_value_poolGrow == 0)
      return ((XML_Char *)NULL);

  }

  {
    enum XML_Convert_Result convert_res;
    enum XML_Convert_Result return_value=enc->utf8Convert(enc, &ptr, end, (ICHAR **)&pool->ptr, (ICHAR *)pool->end);
    convert_res = return_value;
    if(!((signed int)convert_res == 0) && !((signed int)convert_res == 1))
    {
      XML_Bool return_value_poolGrow$0=poolGrow(pool);
      if(return_value_poolGrow$0 == 0)
        return ((XML_Char *)NULL);

    }

  }
  return pool->start;
}

// poolAppendString
// file xmlparse.c line 7121
static const XML_Char * poolAppendString(STRING_POOL *pool, const XML_Char *s)
{
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  while(!(*s == 0))
  {
    __CPROVER_bool tmp_if_expr;
    if(pool->ptr == pool->end)
    {
      return_value_poolGrow=poolGrow(pool);
      tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post = pool->ptr;
      pool->ptr = pool->ptr + 1l;
      *tmp_post = *s;
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return ((const XML_Char *)NULL);

    s = s + 1l;
  }
  return pool->start;
}

// poolBytesToAllocateFor
// file xmlparse.c line 7142
static size_t poolBytesToAllocateFor(signed int blockSize)
{
  const size_t stretch=sizeof(XML_Char) /*1ul*/ ;
  if(!(blockSize >= 1))
    return 0ul;

  else
    if(!((signed int)(2147483647ul / stretch) >= blockSize))
      return 0ul;

    else
    {
      const signed int stretchedBlockSize=blockSize * (signed int)stretch;
      const signed int bytesToAllocate=(signed int)(12ul + (unsigned long int)(unsigned int)stretchedBlockSize);
      if(!(bytesToAllocate >= 0))
        return 0ul;

      else
        return (size_t)bytesToAllocate;
    }
}

// poolClear
// file xmlparse.c line 7033
static void poolClear(STRING_POOL *pool)
{
  if(pool->freeBlocks == ((BLOCK *)NULL))
    pool->freeBlocks = pool->blocks;

  else
  {
    BLOCK *p=pool->blocks;
    while(!(p == ((BLOCK *)NULL)))
    {
      BLOCK *tem=p->next;
      p->next = pool->freeBlocks;
      pool->freeBlocks = p;
      p = tem;
    }
  }
  pool->blocks = ((BLOCK *)NULL);
  pool->start = ((XML_Char *)NULL);
  pool->ptr = ((XML_Char *)NULL);
  pool->end = ((const XML_Char *)NULL);
}

// poolCopyString
// file xmlparse.c line 7085
static const XML_Char * poolCopyString(STRING_POOL *pool, const XML_Char *s)
{
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post$0;
  const XML_Char *tmp_post;
  do
  {
    __CPROVER_bool tmp_if_expr;
    if(pool->ptr == pool->end)
    {
      return_value_poolGrow=poolGrow(pool);
      tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post$0 = pool->ptr;
      pool->ptr = pool->ptr + 1l;
      *tmp_post$0 = *s;
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return ((const XML_Char *)NULL);

    tmp_post = s;
    s = s + 1l;
  }
  while(!(*tmp_post == 0));
  s = pool->start;
  pool->start = pool->ptr;
  return s;
}

// poolCopyStringN
// file xmlparse.c line 7096
static const XML_Char * poolCopyStringN(STRING_POOL *pool, const XML_Char *s, signed int n)
{
  XML_Bool return_value_poolGrow;
  if(pool->ptr == ((XML_Char *)NULL))
  {
    return_value_poolGrow=poolGrow(pool);
    if(return_value_poolGrow == 0)
      return ((const XML_Char *)NULL);

  }

  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post;
  for( ; n >= 1; s = s + 1l)
  {
    __CPROVER_bool tmp_if_expr;
    if(pool->ptr == pool->end)
    {
      return_value_poolGrow$0=poolGrow(pool);
      tmp_if_expr = !(return_value_poolGrow$0 != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post = pool->ptr;
      pool->ptr = pool->ptr + 1l;
      *tmp_post = *s;
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return ((const XML_Char *)NULL);

    n = n - 1;
  }
  s = pool->start;
  pool->start = pool->ptr;
  return s;
}

// poolDestroy
// file xmlparse.c line 7052
static void poolDestroy(STRING_POOL *pool)
{
  BLOCK *p=pool->blocks;
  if(!(p == ((BLOCK *)NULL)))
  {
    BLOCK *tem=p->next;
    pool->mem->free_fcn((void *)p);
    p = tem;
  }

  p = pool->freeBlocks;
  if(!(p == ((BLOCK *)NULL)))
  {
    BLOCK *poolDestroy$$1$$2$$tem=p->next;
    pool->mem->free_fcn((void *)p);
    p = poolDestroy$$1$$2$$tem;
  }

}

// poolGrow
// file xmlparse.c line 7170
static XML_Bool poolGrow(STRING_POOL *pool)
{
  if(!(pool->freeBlocks == ((BLOCK *)NULL)))
  {
    if(pool->start == ((XML_Char *)NULL))
    {
      pool->blocks = pool->freeBlocks;
      pool->freeBlocks = pool->freeBlocks->next;
      pool->blocks->next = ((struct block *)NULL);
      pool->start = pool->blocks->s;
      pool->end = pool->start + (signed long int)pool->blocks->size;
      pool->ptr = pool->start;
      return 1;
    }

    if(!(pool->end - pool->start >= (signed long int)pool->freeBlocks->size))
    {
      BLOCK *tem=pool->freeBlocks->next;
      pool->freeBlocks->next = pool->blocks;
      pool->blocks = pool->freeBlocks;
      pool->freeBlocks = tem;
      memcpy((void *)pool->blocks->s, (const void *)pool->start, (unsigned long int)(pool->end - pool->start) * sizeof(XML_Char) /*1ul*/ );
      pool->ptr = pool->blocks->s + (pool->ptr - pool->start);
      pool->start = pool->blocks->s;
      pool->end = pool->start + (signed long int)pool->blocks->size;
      return 1;
    }

  }

  __CPROVER_bool tmp_if_expr;
  if(!(pool->blocks == ((BLOCK *)NULL)))
    tmp_if_expr = pool->start == pool->blocks->s ? 1 : 0;

  else
    tmp_if_expr = 0;
  if(tmp_if_expr)
  {
    BLOCK *temp;
    signed int poolGrow$$1$$2$$blockSize=(signed int)((unsigned int)(pool->end - pool->start) * 2u);
    size_t bytesToAllocate;
    const ptrdiff_t offsetInsideBlock=pool->ptr - pool->start;
    if(!(poolGrow$$1$$2$$blockSize >= 0))
      return 0;

    bytesToAllocate=poolBytesToAllocateFor(poolGrow$$1$$2$$blockSize);
    if(bytesToAllocate == 0ul)
      return 0;

    void *return_value=pool->mem->realloc_fcn((void *)pool->blocks, (size_t)(unsigned int)bytesToAllocate);
    temp = (BLOCK *)return_value;
    if(temp == ((BLOCK *)NULL))
      return 0;

    pool->blocks = temp;
    pool->blocks->size = poolGrow$$1$$2$$blockSize;
    pool->ptr = pool->blocks->s + offsetInsideBlock;
    pool->start = pool->blocks->s;
    pool->end = pool->start + (signed long int)poolGrow$$1$$2$$blockSize;
  }

  else
  {
    BLOCK *poolGrow$$1$$3$$tem;
    signed int blockSize=(signed int)(pool->end - pool->start);
    size_t poolGrow$$1$$3$$bytesToAllocate;
    if(!(blockSize >= 0))
      return 0;

    if(!(blockSize >= 1024))
      blockSize = 1024;

    else
    {
      if(!((signed int)(unsigned int)blockSize * 2 >= 0))
        return 0;

      blockSize = blockSize * 2;
    }
    poolGrow$$1$$3$$bytesToAllocate=poolBytesToAllocateFor(blockSize);
    if(poolGrow$$1$$3$$bytesToAllocate == 0ul)
      return 0;

    void *return_value$0=pool->mem->malloc_fcn(poolGrow$$1$$3$$bytesToAllocate);
    poolGrow$$1$$3$$tem = (BLOCK *)return_value$0;
    if(poolGrow$$1$$3$$tem == ((BLOCK *)NULL))
      return 0;

    poolGrow$$1$$3$$tem->size = blockSize;
    poolGrow$$1$$3$$tem->next = pool->blocks;
    pool->blocks = poolGrow$$1$$3$$tem;
    if(!(pool->ptr == pool->start))
      memcpy((void *)poolGrow$$1$$3$$tem->s, (const void *)pool->start, (unsigned long int)(pool->ptr - pool->start) * sizeof(XML_Char) /*1ul*/ );

    pool->ptr = poolGrow$$1$$3$$tem->s + (pool->ptr - pool->start);
    pool->start = poolGrow$$1$$3$$tem->s;
    pool->end = poolGrow$$1$$3$$tem->s + (signed long int)blockSize;
  }
  return 1;
}

// poolInit
// file xmlparse.c line 7023
static void poolInit(STRING_POOL *pool, const XML_Memory_Handling_Suite *ms)
{
  pool->blocks = ((BLOCK *)NULL);
  pool->freeBlocks = ((BLOCK *)NULL);
  pool->start = ((XML_Char *)NULL);
  pool->ptr = ((XML_Char *)NULL);
  pool->end = ((const XML_Char *)NULL);
  pool->mem = ms;
}

// poolStoreString
// file xmlparse.c line 7131
static XML_Char * poolStoreString(STRING_POOL *pool, const ENCODING *enc, const char *ptr, const char *end)
{
  XML_Char *return_value_poolAppend=poolAppend(pool, enc, ptr, end);
  XML_Bool return_value_poolGrow;
  if(return_value_poolAppend == ((XML_Char *)NULL))
    return ((XML_Char *)NULL);

  else
  {
    if(pool->ptr == pool->end)
    {
      return_value_poolGrow=poolGrow(pool);
      if(return_value_poolGrow == 0)
        return ((XML_Char *)NULL);

    }

    XML_Char *tmp_post=pool->ptr;
    pool->ptr = pool->ptr + 1l;
    *tmp_post = 0;
    return pool->start;
  }
}

// processInternalEntity
// file xmlparse.c line 5579
static enum XML_Error processInternalEntity(XML_Parser parser, ENTITY *entity, XML_Bool betweenDecl)
{
  const char *textStart;
  const char *textEnd;
  const char *next;
  enum XML_Error result;
  OPEN_INTERNAL_ENTITY *openEntity;
  if(!(parser->m_freeInternalEntities == ((OPEN_INTERNAL_ENTITY *)NULL)))
  {
    openEntity = parser->m_freeInternalEntities;
    parser->m_freeInternalEntities = openEntity->next;
  }

  else
  {
    void *return_value=parser->m_mem.malloc_fcn(sizeof(OPEN_INTERNAL_ENTITY) /*40ul*/ );
    openEntity = (OPEN_INTERNAL_ENTITY *)return_value;
    if(openEntity == ((OPEN_INTERNAL_ENTITY *)NULL))
      return /*enum*/XML_ERROR_NO_MEMORY;

  }
  entity->open = 1;
  entityTrackingOnOpen(parser, entity, 5596);
  entity->processed = 0;
  openEntity->next = parser->m_openInternalEntities;
  parser->m_openInternalEntities = openEntity;
  openEntity->entity = entity;
  openEntity->startTagLevel = parser->m_tagLevel;
  openEntity->betweenDecl = betweenDecl;
  openEntity->internalEventPtr = ((const char *)NULL);
  openEntity->internalEventEndPtr = ((const char *)NULL);
  textStart = (const char *)entity->textPtr;
  textEnd = (const char *)(entity->textPtr + (signed long int)entity->textLen);
  next = textStart;
  if(!(entity->is_param == 0))
  {
    signed int tok;
    signed int return_value$0=parser->m_internalEncoding->scanners[0l](parser->m_internalEncoding, textStart, textEnd, &next);
    tok = return_value$0;
    result=doProlog(parser, parser->m_internalEncoding, textStart, textEnd, tok, next, &next, 0, 0, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
  }

  else
    result=doContent(parser, parser->m_tagLevel, parser->m_internalEncoding, textStart, textEnd, &next, 0, /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
  if((signed int)result == 0)
  {
    __CPROVER_bool tmp_if_expr;
    if(!(textEnd == next))
      tmp_if_expr = (signed int)parser->m_parsingStatus.parsing == 3 ? 1 : 0;

    else
      tmp_if_expr = 0;
    if(tmp_if_expr)
    {
      entity->processed = (signed int)(next - textStart);
      parser->m_processor = internalEntityProcessor;
    }

    else
    {
      entityTrackingOnClose(parser, entity, 5630);
      entity->open = 0;
      parser->m_openInternalEntities = openEntity->next;
      openEntity->next = parser->m_freeInternalEntities;
      parser->m_freeInternalEntities = openEntity;
    }
  }

  return result;
}

// processXmlDecl
// file xmlparse.c line 4141
static enum XML_Error processXmlDecl(XML_Parser parser, signed int isGeneralTextEntity, const char *s, const char *next)
{
  const char *encodingName=((const char *)NULL);
  const XML_Char *storedEncName=((const XML_Char *)NULL);
  const ENCODING *newEncoding=((const ENCODING *)NULL);
  const char *version=((const char *)NULL);
  const char *versionend;
  const XML_Char *storedversion=((const XML_Char *)NULL);
  signed int standalone=-1;
  XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, 12, s, next, 4152, /*enum*/XML_ACCOUNT_DIRECT);
  __CPROVER_bool tmp_if_expr;
  if(return_value_accountingDiffTolerated == 0)
  {
    accountingOnAbort(parser);
    return /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
  }

  else
  {
    signed int return_value=(parser->m_ns != 0 ? XmlParseXmlDeclNS : XmlParseXmlDecl)(isGeneralTextEntity, parser->m_encoding, s, next, &parser->m_eventPtr, &version, &versionend, &encodingName, &newEncoding, &standalone);
    if(return_value == 0)
    {
      if(!(isGeneralTextEntity == 0))
        return /*enum*/XML_ERROR_TEXT_DECL;

      else
        return /*enum*/XML_ERROR_XML_DECL;
    }

    if(isGeneralTextEntity == 0 && standalone == 1)
    {
      parser->m_dtd->standalone = 1;
      if((signed int)parser->m_paramEntityParsing == 1)
        parser->m_paramEntityParsing = /*enum*/XML_PARAM_ENTITY_PARSING_NEVER;

    }

    if(!(parser->m_xmlDeclHandler == ((XML_XmlDeclHandler)NULL)))
    {
      if(!(encodingName == ((const char *)NULL)))
      {
        signed int return_value$0=parser->m_encoding->nameLength(parser->m_encoding, encodingName);
        storedEncName=poolStoreString(&parser->m_temp2Pool, parser->m_encoding, encodingName, encodingName + (signed long int)return_value$0);
        if(storedEncName == ((const XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        (&parser->m_temp2Pool)->start = (&parser->m_temp2Pool)->ptr;
      }

      if(!(version == ((const char *)NULL)))
      {
        storedversion=poolStoreString(&parser->m_temp2Pool, parser->m_encoding, version, versionend - (signed long int)parser->m_encoding->minBytesPerChar);
        if(storedversion == ((const XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

      }

      parser->m_xmlDeclHandler(parser->m_handlerArg, storedversion, storedEncName, standalone);
    }

    else
      if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
        reportDefault(parser, parser->m_encoding, s, next);

    if(parser->m_protocolEncodingName == ((const XML_Char *)NULL))
    {
      if(!(newEncoding == ((const ENCODING *)NULL)))
      {
        __CPROVER_bool tmp_if_expr$0;
        if(!(newEncoding->minBytesPerChar == parser->m_encoding->minBytesPerChar))
          tmp_if_expr$0 = 1;

        else
        {
          if(newEncoding->minBytesPerChar == 2)
            tmp_if_expr = newEncoding != parser->m_encoding ? 1 : 0;

          else
            tmp_if_expr = 0;
          tmp_if_expr$0 = tmp_if_expr ? 1 : 0;
        }
        if(tmp_if_expr$0)
        {
          parser->m_eventPtr = encodingName;
          return /*enum*/XML_ERROR_INCORRECT_ENCODING;
        }

        parser->m_encoding = newEncoding;
      }

      else
        if(!(encodingName == ((const char *)NULL)))
        {
          enum XML_Error result;
          if(storedEncName == ((const XML_Char *)NULL))
          {
            signed int return_value$1=parser->m_encoding->nameLength(parser->m_encoding, encodingName);
            storedEncName=poolStoreString(&parser->m_temp2Pool, parser->m_encoding, encodingName, encodingName + (signed long int)return_value$1);
            if(storedEncName == ((const XML_Char *)NULL))
              return /*enum*/XML_ERROR_NO_MEMORY;

          }

          result=handleUnknownEncoding(parser, storedEncName);
          poolClear(&parser->m_temp2Pool);
          if((signed int)result == 18)
            parser->m_eventPtr = encodingName;

          return result;
        }

    }

    if(!(storedEncName == ((const XML_Char *)NULL)) || !(storedversion == ((const XML_Char *)NULL)))
      poolClear(&parser->m_temp2Pool);

    return /*enum*/XML_ERROR_NONE;
  }
}

// prologInitProcessor
// file xmlparse.c line 4267
static enum XML_Error prologInitProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  enum XML_Error result;
  enum XML_Error return_value_initializeEncoding=initializeEncoding(parser);
  result = return_value_initializeEncoding;
  if(!((signed int)result == 0))
    return result;

  else
  {
    parser->m_processor = prologProcessor;
    enum XML_Error return_value_prologProcessor=prologProcessor(parser, s, end, nextPtr);
    return return_value_prologProcessor;
  }
}

// prologProcessor
// file xmlparse.c line 4467
static enum XML_Error prologProcessor(XML_Parser parser, const char *s, const char *end, const char **nextPtr)
{
  const char *next=s;
  signed int tok;
  signed int return_value=parser->m_encoding->scanners[0l](parser->m_encoding, s, end, &next);
  tok = return_value;
  enum XML_Error return_value_doProlog=doProlog(parser, parser->m_encoding, s, end, tok, next, nextPtr, (XML_Bool)!(parser->m_parsingStatus.finalBuffer != 0), 1, /*enum*/XML_ACCOUNT_DIRECT);
  return return_value_doProlog;
}

// reportComment
// file xmlparse.c line 6168
static signed int reportComment(XML_Parser parser, const ENCODING *enc, const char *start, const char *end)
{
  XML_Char *data;
  if(parser->m_commentHandler == ((XML_CommentHandler)NULL))
  {
    if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
      reportDefault(parser, enc, start, end);

    return 1;
  }

  else
  {
    data=poolStoreString(&parser->m_tempPool, enc, start + (signed long int)(enc->minBytesPerChar * 4), end - (signed long int)(enc->minBytesPerChar * 3));
    if(data == ((XML_Char *)NULL))
      return 0;

    else
    {
      normalizeLines(data);
      parser->m_commentHandler(parser->m_handlerArg, data);
      poolClear(&parser->m_tempPool);
      return 1;
    }
  }
}

// reportDefault
// file xmlparse.c line 6188
static void reportDefault(XML_Parser parser, const ENCODING *enc, const char *s, const char *end)
{
  if(enc->isUtf8 == 0)
  {
    enum XML_Convert_Result convert_res;
    const char **eventPP;
    const char **eventEndPP;
    if(enc == parser->m_encoding)
    {
      eventPP = &parser->m_eventPtr;
      eventEndPP = &parser->m_eventEndPtr;
    }

    else
    {
      eventPP = &parser->m_openInternalEntities->internalEventPtr;
      eventEndPP = &parser->m_openInternalEntities->internalEventEndPtr;
    }
    ICHAR *dataPtr=(ICHAR *)parser->m_dataBuf;
    convert_res=enc->utf8Convert(enc, &s, end, &dataPtr, (ICHAR *)parser->m_dataBufEnd);
    *eventEndPP = s;
    parser->m_defaultHandler(parser->m_handlerArg, parser->m_dataBuf, (signed int)(dataPtr - (ICHAR *)parser->m_dataBuf));
    *eventPP = s;
  }

  else
    parser->m_defaultHandler(parser->m_handlerArg, (XML_Char *)s, (signed int)((XML_Char *)end - (XML_Char *)s));
}

// reportProcessingInstruction
// file xmlparse.c line 6141
static signed int reportProcessingInstruction(XML_Parser parser, const ENCODING *enc, const char *start, const char *end)
{
  const XML_Char *target;
  XML_Char *data;
  const char *tem;
  if(parser->m_processingInstructionHandler == ((XML_ProcessingInstructionHandler)NULL))
  {
    if(!(parser->m_defaultHandler == ((XML_DefaultHandler)NULL)))
      reportDefault(parser, enc, start, end);

    return 1;
  }

  else
  {
    start = start + (signed long int)(enc->minBytesPerChar * 2);
    signed int return_value=enc->nameLength(enc, start);
    tem = start + (signed long int)return_value;
    target=poolStoreString(&parser->m_tempPool, enc, start, tem);
    if(target == ((const XML_Char *)NULL))
      return 0;

    else
    {
      (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
      const char *return_value$0=enc->skipS(enc, tem);
      data=poolStoreString(&parser->m_tempPool, enc, return_value$0, end - (signed long int)(enc->minBytesPerChar * 2));
      if(data == ((XML_Char *)NULL))
        return 0;

      else
      {
        normalizeLines(data);
        parser->m_processingInstructionHandler(parser->m_handlerArg, target, data);
        poolClear(&parser->m_tempPool);
        return 1;
      }
    }
  }
}

// setContext
// file xmlparse.c line 6483
static XML_Bool setContext(XML_Parser parser, const XML_Char *context)
{
  DTD * const dtd=parser->m_dtd;
  const XML_Char *s=context;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post$0;
  __CPROVER_bool tmp_if_expr$3;
  __CPROVER_bool tmp_if_expr$4;
  XML_Bool return_value_poolGrow$1;
  signed int tmp_if_expr$5;
  XML_Char *tmp_post$1;
  XML_Bool return_value_poolGrow$2;
  XML_Char *tmp_post$2;
  XML_Bool return_value_poolGrow$3;
  XML_Char *tmp_post$3;
  while(!((signed int)*context == 0))
  {
    __CPROVER_bool tmp_if_expr$10;
    if((signed int)*s == 0xC)
      tmp_if_expr$10 = 1;

    else
      tmp_if_expr$10 = (signed int)*s == 0 ? 1 : 0;
    if(tmp_if_expr$10)
    {
      ENTITY *e;
      __CPROVER_bool tmp_if_expr;
      if(parser->m_tempPool.ptr == parser->m_tempPool.end)
      {
        return_value_poolGrow=poolGrow(&parser->m_tempPool);
        tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
      }

      else
        tmp_if_expr = 0;
      signed int tmp_if_expr$0;
      if(tmp_if_expr)
        tmp_if_expr$0 = 0;

      else
      {
        tmp_post = (&parser->m_tempPool)->ptr;
        (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
        *tmp_post = 0;
        tmp_if_expr$0 = 1;
      }
      if(tmp_if_expr$0 == 0)
        return 0;

      NAMED *return_value_lookup=lookup(parser, &dtd->generalEntities, (&parser->m_tempPool)->start, 0ul);
      e = (ENTITY *)return_value_lookup;
      if(!(e == ((ENTITY *)NULL)))
        e->open = 1;

      if(!((signed int)*s == 0))
        s = s + 1l;

      context = s;
      (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->start;
    }

    else
      if((signed int)*s == 0x3D)
      {
        PREFIX *prefix;
        if(parser->m_tempPool.ptr - parser->m_tempPool.start == 0l)
          prefix = &dtd->defaultPrefix;

        else
        {
          __CPROVER_bool tmp_if_expr$1;
          if(parser->m_tempPool.ptr == parser->m_tempPool.end)
          {
            return_value_poolGrow$0=poolGrow(&parser->m_tempPool);
            tmp_if_expr$1 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
          }

          else
            tmp_if_expr$1 = 0;
          signed int tmp_if_expr$2;
          if(tmp_if_expr$1)
            tmp_if_expr$2 = 0;

          else
          {
            tmp_post$0 = (&parser->m_tempPool)->ptr;
            (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
            *tmp_post$0 = 0;
            tmp_if_expr$2 = 1;
          }
          if(tmp_if_expr$2 == 0)
            return 0;

          NAMED *return_value_lookup$0=lookup(parser, &dtd->prefixes, (&parser->m_tempPool)->start, sizeof(PREFIX) /*16ul*/ );
          prefix = (PREFIX *)return_value_lookup$0;
          if(prefix == ((PREFIX *)NULL))
            return 0;

          if(prefix->name == parser->m_tempPool.start)
          {
            const XML_Char *return_value_poolCopyString=poolCopyString(&dtd->pool, prefix->name);
            prefix->name = return_value_poolCopyString;
            if(prefix->name == ((const XML_Char *)NULL))
              return 0;

          }

          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->start;
        }
        context = s + 1l;
        do
        {
          if(!((signed int)*context == 0xC))
            tmp_if_expr$3 = (signed int)*context != 0 ? 1 : 0;

          else
            tmp_if_expr$3 = 0;
          if(!tmp_if_expr$3)
            break;

          if(parser->m_tempPool.ptr == parser->m_tempPool.end)
          {
            return_value_poolGrow$1=poolGrow(&parser->m_tempPool);
            tmp_if_expr$4 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
          }

          else
            tmp_if_expr$4 = 0;
          if(tmp_if_expr$4)
            tmp_if_expr$5 = 0;

          else
          {
            tmp_post$1 = (&parser->m_tempPool)->ptr;
            (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
            *tmp_post$1 = *context;
            tmp_if_expr$5 = 1;
          }
          if(tmp_if_expr$5 == 0)
            return 0;

          context = context + 1l;
        }
        while(1);
        __CPROVER_bool tmp_if_expr$6;
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$2=poolGrow(&parser->m_tempPool);
          tmp_if_expr$6 = !(return_value_poolGrow$2 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$6 = 0;
        signed int tmp_if_expr$7;
        if(tmp_if_expr$6)
          tmp_if_expr$7 = 0;

        else
        {
          tmp_post$2 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$2 = 0;
          tmp_if_expr$7 = 1;
        }
        if(tmp_if_expr$7 == 0)
          return 0;

        enum XML_Error return_value_addBinding=addBinding(parser, prefix, ((const ATTRIBUTE_ID *)NULL), (&parser->m_tempPool)->start, &parser->m_inheritedBindings);
        if(!((signed int)return_value_addBinding == 0))
          return 0;

        (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->start;
        if(!((signed int)*context == 0))
          context = context + 1l;

        s = context;
      }

      else
      {
        __CPROVER_bool tmp_if_expr$8;
        if(parser->m_tempPool.ptr == parser->m_tempPool.end)
        {
          return_value_poolGrow$3=poolGrow(&parser->m_tempPool);
          tmp_if_expr$8 = !(return_value_poolGrow$3 != 0) ? 1 : 0;
        }

        else
          tmp_if_expr$8 = 0;
        signed int tmp_if_expr$9;
        if(tmp_if_expr$8)
          tmp_if_expr$9 = 0;

        else
        {
          tmp_post$3 = (&parser->m_tempPool)->ptr;
          (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
          *tmp_post$3 = *s;
          tmp_if_expr$9 = 1;
        }
        if(tmp_if_expr$9 == 0)
          return 0;

        s = s + 1l;
      }
  }
  return 1;
}

// setElementTypePrefix
// file xmlparse.c line 6295
static signed int setElementTypePrefix(XML_Parser parser, ELEMENT_TYPE *elementType)
{
  DTD * const dtd=parser->m_dtd;
  const XML_Char *name=elementType->name;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post$0;
  for( ; !(*name == 0); name = name + 1l)
    if((signed int)*name == 0x3A)
    {
      PREFIX *prefix;
      const XML_Char *s=elementType->name;
      for( ; !(s == name); s = s + 1l)
      {
        __CPROVER_bool tmp_if_expr;
        if(dtd->pool.ptr == dtd->pool.end)
        {
          return_value_poolGrow=poolGrow(&dtd->pool);
          tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
        }

        else
          tmp_if_expr = 0;
        signed int tmp_if_expr$0;
        if(tmp_if_expr)
          tmp_if_expr$0 = 0;

        else
        {
          tmp_post = (&dtd->pool)->ptr;
          (&dtd->pool)->ptr = (&dtd->pool)->ptr + 1l;
          *tmp_post = *s;
          tmp_if_expr$0 = 1;
        }
        if(tmp_if_expr$0 == 0)
          return 0;

      }
      __CPROVER_bool tmp_if_expr$1;
      if(dtd->pool.ptr == dtd->pool.end)
      {
        return_value_poolGrow$0=poolGrow(&dtd->pool);
        tmp_if_expr$1 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
      }

      else
        tmp_if_expr$1 = 0;
      signed int tmp_if_expr$2;
      if(tmp_if_expr$1)
        tmp_if_expr$2 = 0;

      else
      {
        tmp_post$0 = (&dtd->pool)->ptr;
        (&dtd->pool)->ptr = (&dtd->pool)->ptr + 1l;
        *tmp_post$0 = 0;
        tmp_if_expr$2 = 1;
      }
      if(tmp_if_expr$2 == 0)
        return 0;

      NAMED *return_value_lookup=lookup(parser, &dtd->prefixes, (&dtd->pool)->start, sizeof(PREFIX) /*16ul*/ );
      prefix = (PREFIX *)return_value_lookup;
      if(prefix == ((PREFIX *)NULL))
        return 0;

      if(prefix->name == dtd->pool.start)
        (&dtd->pool)->start = (&dtd->pool)->ptr;

      else
        (&dtd->pool)->ptr = (&dtd->pool)->start;
      elementType->prefix = prefix;
      break;
    }

  return 1;
}

// sip24_final
// file siphash.h line 231
static uint64_t sip24_final(struct siphash *H)
{
  const char left=(char)(H->p - H->buf);
  uint64_t b=H->c + (unsigned long int)left << 56;
  switch((signed int)left)
  {
    case 7:
      b = b | (uint64_t)H->buf[6l] << 48;
    case 6:
      b = b | (uint64_t)H->buf[5l] << 40;
    case 5:
      b = b | (uint64_t)H->buf[4l] << 32;
    case 4:
      b = b | (uint64_t)H->buf[3l] << 24;
    case 3:
      b = b | (uint64_t)H->buf[2l] << 16;
    case 2:
      b = b | (uint64_t)H->buf[1l] << 8;
    case 1:
      b = b | (uint64_t)H->buf[0l] << 0;
    case 0:
      ;
  }
  H->v3 = H->v3 ^ b;
  sip_round(H, 2);
  H->v0 = H->v0 ^ b;
  H->v2 = H->v2 ^ 255ul;
  sip_round(H, 4);
  return H->v0 ^ H->v1 ^ H->v2 ^ H->v3;
}

// sip24_init
// file siphash.h line 192
static struct siphash * sip24_init(struct siphash *H, const struct sipkey *key)
{
  H->v0 = (1936682341ul << 32 | 1886610805ul) ^ key->k[0l];
  H->v1 = (1685025377ul << 32 | 1852075885ul) ^ key->k[1l];
  H->v2 = (1819895653ul << 32 | 1852142177ul) ^ key->k[0l];
  H->v3 = (1952801890ul << 32 | 2037671283ul) ^ key->k[1l];
  H->p = H->buf;
  H->c = 0ul;
  return H;
}

// sip24_update
// file siphash.h line 207
static struct siphash * sip24_update(struct siphash *H, const void *src, size_t len)
{
  const unsigned char *p=(const unsigned char *)src;
  const unsigned char *pe=p + (signed long int)len;
  uint64_t m;

__CPROVER_DUMP_L1:
  ;
  unsigned char *tmp_post;
  const unsigned char *tmp_post$0;
  while(1)
  {
    if(p < pe)
    {
      if(H->p < H->buf + (signed long int)sizeof(unsigned char [8l]) /*8l*/ )
      {
        tmp_post = H->p;
        H->p = H->p + 1l;
        tmp_post$0 = p;
        p = p + 1l;
        *tmp_post = *tmp_post$0;
        goto __CPROVER_DUMP_L1;
      }

    }

    if(H->p < H->buf + (signed long int)sizeof(unsigned char [8l]) /*8l*/ )
      break;

    m = (uint64_t)H->buf[0l] << 0 | (uint64_t)H->buf[1l] << 8 | (uint64_t)H->buf[2l] << 16 | (uint64_t)H->buf[3l] << 24 | (uint64_t)H->buf[4l] << 32 | (uint64_t)H->buf[5l] << 40 | (uint64_t)H->buf[6l] << 48 | (uint64_t)H->buf[7l] << 56;
    H->v3 = H->v3 ^ m;
    sip_round(H, 2);
    H->v0 = H->v0 ^ m;
    H->p = H->buf;
    H->c = H->c + 8ul;
    if(!(p < pe))
      break;

  }
  return H;
}

// sip24_valid
// file siphash.h line 288
static signed int sip24_valid(void)
{
  unsigned char in[64l];
  struct sipkey k;
  size_t i;
  sip_tokey(&k, (const void *)"\0\\\\\\\a\b\t\n\v\f\r\\");
  i = 0ul;
  for( ; !(i >= sizeof(unsigned char [64l]) /*64ul*/ ); i = i + 1ul)
  {
    in[(signed long int)i] = (unsigned char)i;
    uint64_t return_value_siphash24=siphash24((const void *)in, i, &k);
    static const unsigned char vectors[64l][8l]={ { 49, 14, 14, 221, 71, 219, 111, 114 }, { 253, 103, 220, 147, 197, 57, 248, 116 }, 
    { 90, 79, 169, 217, 9, 128, 108, 13 }, { 45, 126, 251, 215, 150, 102, 103, 133 }, 
    { 183, 135, 113, 39, 224, 148, 39, 207 }, 
    { 141, 166, 153, 205, 100, 85, 118, 24 }, 
    { 206, 227, 254, 88, 110, 70, 201, 203 }, 
    { 55, 209, 1, 139, 245, 0, 2, 171 }, { 98, 36, 147, 154, 121, 245, 245, 147 }, 
    { 176, 228, 169, 11, 223, 130, 0, 158 }, 
    { 243, 185, 221, 148, 197, 187, 93, 122 }, 
    { 167, 173, 107, 34, 70, 47, 179, 244 }, 
    { 251, 229, 14, 134, 188, 143, 30, 117 }, 
    { 144, 61, 132, 192, 39, 86, 234, 20 }, { 238, 242, 122, 142, 144, 202, 35, 247 }, 
    { 229, 69, 190, 73, 97, 202, 41, 161 }, { 219, 155, 194, 87, 127, 204, 42, 63 }, 
    { 148, 71, 190, 44, 245, 233, 154, 105 }, 
    { 156, 211, 141, 150, 240, 179, 193, 75 }, 
    { 189, 97, 121, 167, 29, 201, 109, 187 }, 
    { 152, 238, 162, 26, 242, 92, 214, 190 }, 
    { 199, 103, 59, 46, 176, 203, 242, 208 }, 
    { 136, 62, 163, 227, 149, 103, 83, 147 }, 
    { 200, 206, 92, 205, 140, 3, 12, 168 }, { 148, 175, 73, 246, 198, 80, 173, 184 }, 
    { 234, 184, 133, 138, 222, 146, 225, 188 }, 
    { 243, 21, 187, 91, 184, 53, 216, 23 }, { 173, 207, 107, 7, 99, 97, 46, 47 }, { 165, 201, 29, 167, 172, 170, 77, 222 }, 
    { 113, 101, 149, 135, 102, 80, 162, 166 }, 
    { 40, 239, 73, 92, 83, 163, 135, 173 }, { 66, 195, 65, 216, 250, 146, 216, 50 }, 
    { 206, 124, 242, 114, 47, 81, 39, 113 }, 
    { 227, 120, 89, 249, 70, 35, 243, 167 }, 
    { 56, 18, 5, 187, 26, 176, 224, 18 }, { 174, 151, 161, 15, 212, 52, 224, 21 }, 
    { 180, 163, 21, 8, 190, 255, 77, 49 }, { 129, 57, 98, 41, 240, 144, 121, 2 }, { 77, 12, 244, 158, 229, 212, 220, 202 }, 
    { 92, 115, 51, 106, 118, 216, 191, 154 }, 
    { 208, 167, 4, 83, 107, 169, 62, 14 }, { 146, 89, 88, 252, 214, 66, 12, 173 }, { 169, 21, 194, 155, 200, 6, 115, 24 }, { 149, 43, 121, 243, 188, 10, 166, 212 }, 
    { 242, 29, 242, 228, 29, 69, 53, 249 }, { 135, 87, 117, 25, 4, 143, 83, 169 }, { 16, 165, 108, 245, 223, 205, 154, 219 }, 
    { 235, 117, 9, 92, 205, 152, 108, 208 }, 
    { 81, 169, 203, 158, 203, 163, 18, 230 }, 
    { 150, 175, 173, 252, 44, 230, 102, 199 }, 
    { 114, 254, 82, 151, 90, 67, 100, 238 }, 
    { 90, 22, 69, 178, 118, 213, 146, 161 }, 
    { 178, 116, 203, 142, 191, 135, 135, 10 }, 
    { 111, 155, 180, 32, 61, 231, 179, 129 }, 
    { 234, 236, 178, 163, 11, 34, 168, 127 }, 
    { 153, 36, 164, 60, 193, 49, 87, 36 }, { 189, 131, 141, 58, 175, 191, 141, 183 }, 
    { 11, 26, 42, 50, 101, 213, 26, 234 }, { 19, 80, 121, 163, 35, 28, 230, 96 }, { 147, 43, 40, 70, 228, 215, 6, 102 }, { 225, 145, 95, 92, 177, 236, 164, 108 }, 
    { 243, 37, 150, 92, 161, 109, 98, 159 }, 
    { 87, 95, 242, 142, 96, 56, 27, 229 }, { 114, 69, 6, 235, 76, 50, 138, 149 } };
    if(!(return_value_siphash24 == ((uint64_t)vectors[(signed long int)i][0l] | (uint64_t)vectors[(signed long int)i][1l] << 8 | (uint64_t)vectors[(signed long int)i][2l] << 16 | (uint64_t)vectors[(signed long int)i][3l] << 24 | (uint64_t)vectors[(signed long int)i][4l] << 32 | (uint64_t)vectors[(signed long int)i][5l] << 40 | (uint64_t)vectors[(signed long int)i][6l] << 48 | (uint64_t)vectors[(signed long int)i][7l] << 56)))
      return 0;

  }
  return 1;
}

// sip_round
// file siphash.h line 167
static void sip_round(struct siphash *H, const signed int rounds)
{
  signed int i=0;
  for( ; !(i >= rounds); i = i + 1)
  {
    H->v0 = H->v0 + H->v1;
    H->v1 = (uint64_t)(H->v1 << 13 | H->v1 >> 64 - 13);
    H->v1 = H->v1 ^ H->v0;
    H->v0 = (uint64_t)(H->v0 << 32 | H->v0 >> 64 - 32);
    H->v2 = H->v2 + H->v3;
    H->v3 = (uint64_t)(H->v3 << 16 | H->v3 >> 64 - 16);
    H->v3 = H->v3 ^ H->v2;
    H->v0 = H->v0 + H->v3;
    H->v3 = (uint64_t)(H->v3 << 21 | H->v3 >> 64 - 21);
    H->v3 = H->v3 ^ H->v0;
    H->v2 = H->v2 + H->v1;
    H->v1 = (uint64_t)(H->v1 << 17 | H->v1 >> 64 - 17);
    H->v1 = H->v1 ^ H->v2;
    H->v2 = (uint64_t)(H->v2 << 32 | H->v2 >> 64 - 32);
  }
}

// sip_tokey
// file siphash.h line 148
static struct sipkey * sip_tokey(struct sipkey *key, const void *src)
{
  key->k[0l] = (uint64_t)((const unsigned char *)src)[0l] << 0 | (uint64_t)((const unsigned char *)src)[1l] << 8 | (uint64_t)((const unsigned char *)src)[2l] << 16 | (uint64_t)((const unsigned char *)src)[3l] << 24 | (uint64_t)((const unsigned char *)src)[4l] << 32 | (uint64_t)((const unsigned char *)src)[5l] << 40 | (uint64_t)((const unsigned char *)src)[6l] << 48 | (uint64_t)((const unsigned char *)src)[7l] << 56;
  key->k[1l] = (uint64_t)((const unsigned char *)src + 8l)[0l] << 0 | (uint64_t)((const unsigned char *)src + 8l)[1l] << 8 | (uint64_t)((const unsigned char *)src + 8l)[2l] << 16 | (uint64_t)((const unsigned char *)src + 8l)[3l] << 24 | (uint64_t)((const unsigned char *)src + 8l)[4l] << 32 | (uint64_t)((const unsigned char *)src + 8l)[5l] << 40 | (uint64_t)((const unsigned char *)src + 8l)[6l] << 48 | (uint64_t)((const unsigned char *)src + 8l)[7l] << 56;
  return key;
}

// siphash24
// file siphash.h line 271
static uint64_t siphash24(const void *src, size_t len, const struct sipkey *key)
{
  struct siphash state={ .v0=0ul, .v1=0ul, .v2=0ul, .v3=0ul, .buf={ 0, 0, 0, 0, 0, 0, 0, 0 }, .p=((unsigned char *)NULL),
    .c=0ul };
  struct siphash *return_value_sip24_init=sip24_init(&state, key);
  struct siphash *return_value_sip24_update=sip24_update(return_value_sip24_init, src, len);
  uint64_t return_value_sip24_final=sip24_final(return_value_sip24_update);
  return return_value_sip24_final;
}

// startParsing
// file xmlparse.c line 949
static XML_Bool startParsing(XML_Parser parser)
{
  unsigned long int return_value_generate_hash_secret_salt;
  if(parser->m_hash_secret_salt == 0ul)
  {
    return_value_generate_hash_secret_salt=generate_hash_secret_salt(parser);
    parser->m_hash_secret_salt = return_value_generate_hash_secret_salt;
  }

  if(!(parser->m_ns == 0))
  {
    XML_Bool return_value_setContext=setContext(parser, implicitContext);
    return return_value_setContext;
  }

  else
    return 1;
}

// storeAttributeValue
// file xmlparse.c line 5719
static enum XML_Error storeAttributeValue(XML_Parser parser, const ENCODING *enc, XML_Bool isCdata, const char *ptr, const char *end, STRING_POOL *pool, enum XML_Account account)
{
  enum XML_Error result;
  enum XML_Error return_value_appendAttributeValue=appendAttributeValue(parser, enc, isCdata, ptr, end, pool, account);
  result = return_value_appendAttributeValue;
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post;
  if(!(result == /*enum*/XML_ERROR_NONE))
    return result;

  else
  {
    if(isCdata == 0)
    {
      if(!(pool->ptr - pool->start == 0l))
      {
        if((signed int)pool->ptr[-1l] == 0x20)
          pool->ptr = pool->ptr - 1l;

      }

    }

    __CPROVER_bool tmp_if_expr;
    if(pool->ptr == pool->end)
    {
      return_value_poolGrow=poolGrow(pool);
      tmp_if_expr = !(return_value_poolGrow != 0) ? 1 : 0;
    }

    else
      tmp_if_expr = 0;
    signed int tmp_if_expr$0;
    if(tmp_if_expr)
      tmp_if_expr$0 = 0;

    else
    {
      tmp_post = pool->ptr;
      pool->ptr = pool->ptr + 1l;
      *tmp_post = 0;
      tmp_if_expr$0 = 1;
    }
    if(tmp_if_expr$0 == 0)
      return /*enum*/XML_ERROR_NO_MEMORY;

    else
      return /*enum*/XML_ERROR_NONE;
  }
}

// storeAtts
// file xmlparse.c line 3239
static enum XML_Error storeAtts(XML_Parser parser, const ENCODING *enc, const char *attStr, TAG_NAME *tagNamePtr, BINDING **bindingsPtr, enum XML_Account account)
{
  DTD * const dtd=parser->m_dtd;
  ELEMENT_TYPE *elementType;
  signed int nDefaultAtts;
  const XML_Char **appAtts;
  signed int attIndex=0;
  signed int prefixLen;
  signed int i;
  signed int n;
  XML_Char *uri;
  signed int nPrefixes=0;
  BINDING *binding;
  const XML_Char *localPart;
  NAMED *return_value_lookup=lookup(parser, &dtd->elementTypes, tagNamePtr->str, 0ul);
  elementType = (ELEMENT_TYPE *)return_value_lookup;
  signed int return_value_setElementTypePrefix;
  if(elementType == ((ELEMENT_TYPE *)NULL))
  {
    const XML_Char *name;
    const XML_Char *return_value_poolCopyString=poolCopyString(&dtd->pool, tagNamePtr->str);
    name = return_value_poolCopyString;
    if(name == ((const XML_Char *)NULL))
      return /*enum*/XML_ERROR_NO_MEMORY;

    NAMED *return_value_lookup$0=lookup(parser, &dtd->elementTypes, name, sizeof(ELEMENT_TYPE) /*40ul*/ );
    elementType = (ELEMENT_TYPE *)return_value_lookup$0;
    if(elementType == ((ELEMENT_TYPE *)NULL))
      return /*enum*/XML_ERROR_NO_MEMORY;

    if(!(parser->m_ns == 0))
    {
      return_value_setElementTypePrefix=setElementTypePrefix(parser, elementType);
      if(return_value_setElementTypePrefix == 0)
        return /*enum*/XML_ERROR_NO_MEMORY;

    }

  }

  nDefaultAtts = elementType->nDefaultAtts;
  n=enc->getAtts(enc, attStr, parser->m_attsSize, parser->m_atts);
  XML_Bool return_value_poolGrow;
  XML_Char *tmp_post$5;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post$8;
  XML_Bool return_value_poolGrow$1;
  XML_Char *tmp_post$10;
  if(!(0x7FFFFFFF + -nDefaultAtts >= n))
    return /*enum*/XML_ERROR_NO_MEMORY;

  else
  {
    if(!(parser->m_attsSize >= n + nDefaultAtts))
    {
      signed int oldAttsSize=parser->m_attsSize;
      ATTRIBUTE *storeAtts$$1$$3$$temp;
      if(nDefaultAtts >= 2147483632 || !(0x7FFFFFFF + -(nDefaultAtts + 16) >= n))
        return /*enum*/XML_ERROR_NO_MEMORY;

      parser->m_attsSize = n + nDefaultAtts + 16;
      void *return_value=parser->m_mem.realloc_fcn((void *)parser->m_atts, (unsigned long int)parser->m_attsSize * sizeof(ATTRIBUTE) /*32ul*/ );
      storeAtts$$1$$3$$temp = (ATTRIBUTE *)return_value;
      if(storeAtts$$1$$3$$temp == ((ATTRIBUTE *)NULL))
      {
        parser->m_attsSize = oldAttsSize;
        return /*enum*/XML_ERROR_NO_MEMORY;
      }

      parser->m_atts = storeAtts$$1$$3$$temp;
      if(!(oldAttsSize >= n))
        enc->getAtts(enc, attStr, n, parser->m_atts);

    }

    appAtts = (const XML_Char **)parser->m_atts;
    i = 0;
    if(!(i >= n))
    {
      ATTRIBUTE *currAtt=&parser->m_atts[(signed long int)i];
      ATTRIBUTE_ID *attId;
      signed int return_value$0=enc->nameLength(enc, currAtt->name);
      ATTRIBUTE_ID *return_value_getAttributeId=getAttributeId(parser, enc, currAtt->name, currAtt->name + (signed long int)return_value$0);
      attId = return_value_getAttributeId;
      if(attId == ((ATTRIBUTE_ID *)NULL))
        return /*enum*/XML_ERROR_NO_MEMORY;

      if(!(attId->name[-1l] == 0))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = (parser->m_atts + (signed long int)i)->name;

        return /*enum*/XML_ERROR_DUPLICATE_ATTRIBUTE;
      }

      attId->name[(signed long int)-1] = 1;
      signed int tmp_post=attIndex;
      attIndex = attIndex + 1;
      appAtts[(signed long int)tmp_post] = attId->name;
      if((parser->m_atts + (signed long int)i)->normalized == 0)
      {
        enum XML_Error result;
        XML_Bool isCdata=1;
        if(!(attId->maybeTokenized == 0))
        {
          signed int j=0;
          if(!(j >= nDefaultAtts))
          {
            if(attId == (elementType->defaultAtts + (signed long int)j)->id)
              isCdata = (elementType->defaultAtts + (signed long int)j)->isCdata;

            else
              j = j + 1;
          }

        }

        result=storeAttributeValue(parser, enc, isCdata, (parser->m_atts + (signed long int)i)->valuePtr, (parser->m_atts + (signed long int)i)->valueEnd, &parser->m_tempPool, account);
        if(!(result == /*enum*/XML_ERROR_NONE))
          return result;

        appAtts[(signed long int)attIndex] = (&parser->m_tempPool)->start;
        (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
      }

      else
      {
        XML_Char *return_value_poolStoreString=poolStoreString(&parser->m_tempPool, enc, (parser->m_atts + (signed long int)i)->valuePtr, (parser->m_atts + (signed long int)i)->valueEnd);
        appAtts[(signed long int)attIndex] = return_value_poolStoreString;
        if(appAtts[(signed long int)attIndex] == ((const XML_Char *)NULL))
          return /*enum*/XML_ERROR_NO_MEMORY;

        (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
      }
      if(!(attId->prefix == ((PREFIX *)NULL)))
      {
        if(!(attId->xmlns == 0))
        {
          enum XML_Error storeAtts$$1$$4$$1$$4$$1$$result;
          enum XML_Error return_value_addBinding=addBinding(parser, attId->prefix, attId, appAtts[(signed long int)attIndex], bindingsPtr);
          storeAtts$$1$$4$$1$$4$$1$$result = return_value_addBinding;
          if(!(storeAtts$$1$$4$$1$$4$$1$$result == /*enum*/XML_ERROR_NONE))
            return storeAtts$$1$$4$$1$$4$$1$$result;

          attIndex = attIndex - 1;
        }

        else
        {
          attIndex = attIndex + 1;
          nPrefixes = nPrefixes + 1;
          attId->name[(signed long int)-1] = 2;
        }
      }

      else
        attIndex = attIndex + 1;
      i = i + 1;
    }

    parser->m_nSpecifiedAtts = attIndex;
    __CPROVER_bool tmp_if_expr;
    if(!(elementType->idAtt == ((const ATTRIBUTE_ID *)NULL)))
      tmp_if_expr = elementType->idAtt->name[(signed long int)-1] != 0 ? 1 : 0;

    else
      tmp_if_expr = 0;
    if(tmp_if_expr)
    {
      i = 0;
      if(!(i >= attIndex))
      {
        if(appAtts[(signed long int)i] == elementType->idAtt->name)
          parser->m_idAttIndex = i;

        else
          i = i + 2;
      }

    }

    else
      parser->m_idAttIndex = -1;
    i = 0;
    if(!(i >= nDefaultAtts))
    {
      const DEFAULT_ATTRIBUTE *da=elementType->defaultAtts + (signed long int)i;
      if(da->id->name[-1l] == 0)
      {
        if(!(da->value == ((const XML_Char *)NULL)))
        {
          if(!(da->id->prefix == ((PREFIX *)NULL)))
          {
            if(!(da->id->xmlns == 0))
            {
              enum XML_Error storeAtts$$1$$6$$1$$1$$1$$1$$result;
              enum XML_Error return_value_addBinding$0=addBinding(parser, da->id->prefix, da->id, da->value, bindingsPtr);
              storeAtts$$1$$6$$1$$1$$1$$1$$result = return_value_addBinding$0;
              if(!(storeAtts$$1$$6$$1$$1$$1$$1$$result == /*enum*/XML_ERROR_NONE))
                return storeAtts$$1$$6$$1$$1$$1$$1$$result;

            }

            else
            {
              da->id->name[(signed long int)-1] = 2;
              nPrefixes = nPrefixes + 1;
              signed int tmp_post$0=attIndex;
              attIndex = attIndex + 1;
              appAtts[(signed long int)tmp_post$0] = da->id->name;
              signed int tmp_post$1=attIndex;
              attIndex = attIndex + 1;
              appAtts[(signed long int)tmp_post$1] = da->value;
            }
          }

          else
          {
            da->id->name[(signed long int)-1] = 1;
            signed int tmp_post$2=attIndex;
            attIndex = attIndex + 1;
            appAtts[(signed long int)tmp_post$2] = da->id->name;
            signed int tmp_post$3=attIndex;
            attIndex = attIndex + 1;
            appAtts[(signed long int)tmp_post$3] = da->value;
          }
        }

      }

      i = i + 1;
    }

    appAtts[(signed long int)attIndex] = ((const XML_Char *)NULL);
    i = 0;
    if(!(nPrefixes == 0))
    {
      signed int storeAtts$$1$$7$$j;
      unsigned long int version=parser->m_nsAttsVersion;
      if((unsigned long int)parser->m_nsAttsPower >= sizeof(unsigned int) * 8ul /*32ul*/ )
        return /*enum*/XML_ERROR_NO_MEMORY;

      unsigned int nsAttsSize=1u << (signed int)parser->m_nsAttsPower;
      unsigned char oldNsAttsPower=parser->m_nsAttsPower;
      if(!((nPrefixes << 1) >> (signed int)parser->m_nsAttsPower == 0))
      {
        NS_ATT *temp;
        unsigned char tmp_post$4=parser->m_nsAttsPower;
        parser->m_nsAttsPower = parser->m_nsAttsPower + 1;
        if(!((signed int)parser->m_nsAttsPower >= 3))
          parser->m_nsAttsPower = 3;

        if((unsigned long int)parser->m_nsAttsPower >= sizeof(unsigned int) * 8ul /*32ul*/ )
        {
          parser->m_nsAttsPower = oldNsAttsPower;
          return /*enum*/XML_ERROR_NO_MEMORY;
        }

        nsAttsSize = 1u << (signed int)parser->m_nsAttsPower;
        void *return_value$1=parser->m_mem.realloc_fcn((void *)parser->m_nsAtts, (unsigned long int)nsAttsSize * sizeof(NS_ATT) /*24ul*/ );
        temp = (NS_ATT *)return_value$1;
        if(temp == ((NS_ATT *)NULL))
        {
          parser->m_nsAttsPower = oldNsAttsPower;
          return /*enum*/XML_ERROR_NO_MEMORY;
        }

        parser->m_nsAtts = temp;
        version = 0ul;
      }

      if(version == 0ul)
      {
        version = 4294967295ul;
        storeAtts$$1$$7$$j = (signed int)nsAttsSize;
        if(!(storeAtts$$1$$7$$j == 0))
        {
          storeAtts$$1$$7$$j = storeAtts$$1$$7$$j - 1;
          (parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->version = version;
        }

      }

      version = version - 1ul;
      parser->m_nsAttsVersion = version;
      if(!(i >= attIndex))
      {
        const XML_Char *s=appAtts[(signed long int)i];
        if((signed int)s[-1l] == 2)
        {
          ATTRIBUTE_ID *id;
          const BINDING *b;
          unsigned long int uriHash;
          struct siphash sip_state;
          struct sipkey sip_key;
          copy_salt_to_sipkey(parser, &sip_key);
          sip24_init(&sip_state, &sip_key);
          ((XML_Char *)s)[(signed long int)-1] = 0;
          NAMED *return_value_lookup$1=lookup(parser, &dtd->attributeIds, s, 0ul);
          id = (ATTRIBUTE_ID *)return_value_lookup$1;
          __CPROVER_bool tmp_if_expr$0;
          if(id == ((ATTRIBUTE_ID *)NULL))
            tmp_if_expr$0 = 1;

          else
            tmp_if_expr$0 = !(id->prefix != ((PREFIX *)NULL)) ? 1 : 0;
          if(tmp_if_expr$0)
            return /*enum*/XML_ERROR_NO_MEMORY;

          b = id->prefix->binding;
          if(b == ((const BINDING *)NULL))
            return /*enum*/XML_ERROR_UNBOUND_PREFIX;

          storeAtts$$1$$7$$j = 0;
          if(!(storeAtts$$1$$7$$j >= b->uriLen))
          {
            const XML_Char c=b->uri[(signed long int)storeAtts$$1$$7$$j];
            __CPROVER_bool tmp_if_expr$1;
            if(parser->m_tempPool.ptr == parser->m_tempPool.end)
            {
              return_value_poolGrow=poolGrow(&parser->m_tempPool);
              tmp_if_expr$1 = !(return_value_poolGrow != 0) ? 1 : 0;
            }

            else
              tmp_if_expr$1 = 0;
            signed int tmp_if_expr$2;
            if(tmp_if_expr$1)
              tmp_if_expr$2 = 0;

            else
            {
              tmp_post$5 = (&parser->m_tempPool)->ptr;
              (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
              *tmp_post$5 = c;
              tmp_if_expr$2 = 1;
            }
            if(tmp_if_expr$2 == 0)
              return /*enum*/XML_ERROR_NO_MEMORY;

            storeAtts$$1$$7$$j = storeAtts$$1$$7$$j + 1;
          }

          sip24_update(&sip_state, (const void *)b->uri, (unsigned long int)b->uriLen * sizeof(XML_Char) /*1ul*/ );
          const XML_Char *tmp_post$6=s;
          s = s + 1l;
          size_t return_value_keylen=keylen(s);
          sip24_update(&sip_state, (const void *)s, return_value_keylen * sizeof(XML_Char) /*1ul*/ );
          __CPROVER_bool tmp_if_expr$3;
          if(parser->m_tempPool.ptr == parser->m_tempPool.end)
          {
            return_value_poolGrow$0=poolGrow(&parser->m_tempPool);
            tmp_if_expr$3 = !(return_value_poolGrow$0 != 0) ? 1 : 0;
          }

          else
            tmp_if_expr$3 = 0;
          signed int tmp_if_expr$4;
          if(tmp_if_expr$3)
            tmp_if_expr$4 = 0;

          else
          {
            tmp_post$8 = (&parser->m_tempPool)->ptr;
            (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
            *tmp_post$8 = *s;
            tmp_if_expr$4 = 1;
          }
          if(tmp_if_expr$4 == 0)
            return /*enum*/XML_ERROR_NO_MEMORY;

          const XML_Char *tmp_post$7=s;
          s = s + 1l;
          uint64_t return_value_sip24_final=sip24_final(&sip_state);
          uriHash = (unsigned long int)return_value_sip24_final;
          unsigned char step=0;
          unsigned long int mask=(unsigned long int)(nsAttsSize - 1u);
          storeAtts$$1$$7$$j = (signed int)(uriHash & mask);
          if((parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->version == version)
          {
            if(uriHash == (parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->hash)
            {
              const XML_Char *s1=(&parser->m_tempPool)->start;
              const XML_Char *s2=(parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->uriName;
              __CPROVER_bool tmp_if_expr$5;
              if(*s1 == *s2)
                tmp_if_expr$5 = (signed int)*s1 != 0 ? 1 : 0;

              else
                tmp_if_expr$5 = 0;
              if(tmp_if_expr$5)
              {
                s1 = s1 + 1l;
                s2 = s2 + 1l;
              }

              if((signed int)*s1 == 0)
                return /*enum*/XML_ERROR_DUPLICATE_ATTRIBUTE;

            }

            if(step == 0)
              step = (unsigned char)((uriHash & ~mask) >> (signed int)parser->m_nsAttsPower - 1 & mask >> 2 | 1ul);

            if(!(storeAtts$$1$$7$$j >= (signed int)step))
              storeAtts$$1$$7$$j = (signed int)((unsigned int)storeAtts$$1$$7$$j + (nsAttsSize - (unsigned int)step));

            else
              storeAtts$$1$$7$$j = storeAtts$$1$$7$$j - (signed int)step;
          }

          if(!(parser->m_ns_triplets == 0))
          {
            parser->m_tempPool.ptr[(signed long int)-1] = parser->m_namespaceSeparator;
            s = b->prefix->name;
            __CPROVER_bool tmp_if_expr$6;
            if(parser->m_tempPool.ptr == parser->m_tempPool.end)
            {
              return_value_poolGrow$1=poolGrow(&parser->m_tempPool);
              tmp_if_expr$6 = !(return_value_poolGrow$1 != 0) ? 1 : 0;
            }

            else
              tmp_if_expr$6 = 0;
            signed int tmp_if_expr$7;
            if(tmp_if_expr$6)
              tmp_if_expr$7 = 0;

            else
            {
              tmp_post$10 = (&parser->m_tempPool)->ptr;
              (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->ptr + 1l;
              *tmp_post$10 = *s;
              tmp_if_expr$7 = 1;
            }
            if(tmp_if_expr$7 == 0)
              return /*enum*/XML_ERROR_NO_MEMORY;

            const XML_Char *tmp_post$9=s;
            s = s + 1l;
          }

          s = (&parser->m_tempPool)->start;
          (&parser->m_tempPool)->start = (&parser->m_tempPool)->ptr;
          appAtts[(signed long int)i] = s;
          (parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->version = version;
          (parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->hash = uriHash;
          (parser->m_nsAtts + (signed long int)storeAtts$$1$$7$$j)->uriName = s;
          nPrefixes = nPrefixes - 1;
          if(nPrefixes == 0)
            i = i + 2;

        }

        else
          ((XML_Char *)s)[(signed long int)-1] = 0;
        i = i + 2;
      }

    }

    if(!(i >= attIndex))
    {
      ((XML_Char *)appAtts[(signed long int)i])[(signed long int)-1] = 0;
      i = i + 2;
    }

    binding = *bindingsPtr;
    if(!(binding == ((BINDING *)NULL)))
    {
      binding->attId->name[(signed long int)-1] = 0;
      binding = binding->nextTagBinding;
    }

    if(parser->m_ns == 0)
      return /*enum*/XML_ERROR_NONE;

    else
    {
      if(!(elementType->prefix == ((PREFIX *)NULL)))
      {
        binding = elementType->prefix->binding;
        if(binding == ((BINDING *)NULL))
          return /*enum*/XML_ERROR_UNBOUND_PREFIX;

        localPart = tagNamePtr->str;
        const XML_Char *tmp_post$11=localPart;
        localPart = localPart + 1l;
      }

      else
        if(!(dtd->defaultPrefix.binding == ((BINDING *)NULL)))
        {
          binding = dtd->defaultPrefix.binding;
          localPart = tagNamePtr->str;
        }

        else
          return /*enum*/XML_ERROR_NONE;
      prefixLen = 0;
      if(!(parser->m_ns_triplets == 0))
      {
        if(!(binding->prefix->name == ((const XML_Char *)NULL)))
        {
          signed int tmp_post$12=prefixLen;
          prefixLen = prefixLen + 1;
        }

      }

      tagNamePtr->localPart = localPart;
      tagNamePtr->uriLen = binding->uriLen;
      tagNamePtr->prefix = binding->prefix->name;
      tagNamePtr->prefixLen = prefixLen;
      i = 0;
      signed int tmp_post$13=i;
      i = i + 1;
      __CPROVER_bool tmp_if_expr$8;
      if(!(0x7FFFFFFF + -prefixLen >= binding->uriLen))
        tmp_if_expr$8 = 1;

      else
        tmp_if_expr$8 = i > 0x7FFFFFFF - (binding->uriLen + prefixLen) ? 1 : 0;
      if(tmp_if_expr$8)
        return /*enum*/XML_ERROR_NO_MEMORY;

      else
      {
        n = i + binding->uriLen + prefixLen;
        if(!(binding->uriAlloc >= n))
        {
          TAG *p;
          if(n >= 2147483624)
            return /*enum*/XML_ERROR_NO_MEMORY;

          void *return_value$2=parser->m_mem.malloc_fcn((unsigned long int)(n + 24) * sizeof(XML_Char) /*1ul*/ );
          uri = (XML_Char *)return_value$2;
          if(uri == ((XML_Char *)NULL))
            return /*enum*/XML_ERROR_NO_MEMORY;

          binding->uriAlloc = n + 24;
          memcpy((void *)uri, (const void *)binding->uri, (unsigned long int)binding->uriLen * sizeof(XML_Char) /*1ul*/ );
          p = parser->m_tagStack;
          if(!(p == ((TAG *)NULL)))
          {
            if(p->name.str == binding->uri)
              p->name.str = uri;

            p = p->parent;
          }

          parser->m_mem.free_fcn((void *)binding->uri);
          binding->uri = uri;
        }

        uri = binding->uri + (signed long int)binding->uriLen;
        memcpy((void *)uri, (const void *)localPart, (unsigned long int)i * sizeof(XML_Char) /*1ul*/ );
        if(!(prefixLen == 0))
        {
          uri = uri + (signed long int)(i - 1);
          *uri = parser->m_namespaceSeparator;
          memcpy((void *)(uri + 1l), (const void *)binding->prefix->name, (unsigned long int)prefixLen * sizeof(XML_Char) /*1ul*/ );
        }

        tagNamePtr->str = binding->uri;
        return /*enum*/XML_ERROR_NONE;
      }
    }
  }
}

// storeEntityValue
// file xmlparse.c line 5934
static enum XML_Error storeEntityValue(XML_Parser parser, const ENCODING *enc, const char *entityTextPtr, const char *entityTextEnd, enum XML_Account account)
{
  DTD * const dtd=parser->m_dtd;
  STRING_POOL *pool=&dtd->entityValuePool;
  enum XML_Error result=/*enum*/XML_ERROR_NONE;
  signed int oldInEntityValue=parser->m_prologState.inEntityValue;
  parser->m_prologState.inEntityValue = 1;
  if(pool->blocks == ((BLOCK *)NULL))
  {
    XML_Bool return_value_poolGrow=poolGrow(pool);
    if(return_value_poolGrow == 0)
      return /*enum*/XML_ERROR_NO_MEMORY;

  }

  __CPROVER_bool tmp_if_expr;
  XML_Char *return_value_poolAppend;
  XML_Bool return_value_poolGrow$0;
  XML_Char *tmp_post;
  XML_Bool return_value_poolGrow$1;
  {
    const char *next=entityTextPtr;
    signed int tok;
    signed int return_value=enc->literalScanners[1l](enc, entityTextPtr, entityTextEnd, &next);
    tok = return_value;
    XML_Bool return_value_accountingDiffTolerated=accountingDiffTolerated(parser, tok, entityTextPtr, next, 5960, account);
    if(return_value_accountingDiffTolerated == 0)
    {
      accountingOnAbort(parser);
      result = /*enum*/XML_ERROR_AMPLIFICATION_LIMIT_BREACH;
    }

    if(tok == 28)
    {
      if(!(parser->m_isParamEntity == 0))
        tmp_if_expr = 1;

      else
        tmp_if_expr = enc != parser->m_encoding ? 1 : 0;
      if(tmp_if_expr)
      {
        const XML_Char *name;
        ENTITY *entity;
        name=poolStoreString(&parser->m_tempPool, enc, entityTextPtr + (signed long int)enc->minBytesPerChar, next - (signed long int)enc->minBytesPerChar);
        if(name == ((const XML_Char *)NULL))
          result = /*enum*/XML_ERROR_NO_MEMORY;

        NAMED *return_value_lookup=lookup(parser, &dtd->paramEntities, name, 0ul);
        entity = (ENTITY *)return_value_lookup;
        (&parser->m_tempPool)->ptr = (&parser->m_tempPool)->start;
        if(entity == ((ENTITY *)NULL))
          dtd->keepProcessing = dtd->standalone;

        if(!(entity->open == 0))
        {
          if(enc == parser->m_encoding)
            parser->m_eventPtr = entityTextPtr;

          result = /*enum*/XML_ERROR_RECURSIVE_ENTITY_REF;
        }

        if(!(entity->systemId == ((const XML_Char *)NULL)))
        {
          if(!(parser->m_externalEntityRefHandler == ((XML_ExternalEntityRefHandler)NULL)))
          {
            dtd->paramEntityRead = 0;
            entity->open = 1;
            entityTrackingOnOpen(parser, entity, 6003);
            signed int return_value$0=parser->m_externalEntityRefHandler(parser->m_externalEntityRefHandlerArg, ((const XML_Char *)NULL), entity->base, entity->systemId, entity->publicId);
            if(return_value$0 == 0)
            {
              entityTrackingOnClose(parser, entity, 6007);
              entity->open = 0;
              result = /*enum*/XML_ERROR_EXTERNAL_ENTITY_HANDLING;
            }

            entityTrackingOnClose(parser, entity, 6012);
            entity->open = 0;
            if(dtd->paramEntityRead == 0)
              dtd->keepProcessing = dtd->standalone;

          }

          else
            dtd->keepProcessing = dtd->standalone;
        }

        else
        {
          entity->open = 1;
          entityTrackingOnOpen(parser, entity, 6020);
          result=storeEntityValue(parser, parser->m_internalEncoding, (const char *)entity->textPtr, (const char *)(entity->textPtr + (signed long int)entity->textLen), /*enum*/XML_ACCOUNT_ENTITY_EXPANSION);
          entityTrackingOnClose(parser, entity, 6025);
          entity->open = 0;
        }
      }

      parser->m_eventPtr = entityTextPtr;
      result = /*enum*/XML_ERROR_PARAM_ENTITY_REF;
      result = /*enum*/XML_ERROR_NONE;
      return_value_poolAppend=poolAppend(pool, enc, entityTextPtr, next);
      if(return_value_poolAppend == ((XML_Char *)NULL))
        result = /*enum*/XML_ERROR_NO_MEMORY;

      next = entityTextPtr + (signed long int)enc->minBytesPerChar;
      if(pool->end == pool->ptr)
      {
        return_value_poolGrow$0=poolGrow(pool);
        if(return_value_poolGrow$0 == 0)
          result = /*enum*/XML_ERROR_NO_MEMORY;

      }

      tmp_post = pool->ptr;
      pool->ptr = pool->ptr + 1l;
      *tmp_post = '\n';
      XML_Char buf[4l];
      signed int i;
      signed int n;
      signed int return_value$1=enc->charRefNumber(enc, entityTextPtr);
      n = return_value$1;
      if(!(n >= 0))
      {
        if(enc == parser->m_encoding)
          parser->m_eventPtr = entityTextPtr;

        result = /*enum*/XML_ERROR_BAD_CHAR_REF;
      }

      n=XmlUtf8Encode(n, (ICHAR *)buf);
      i = 0;
      if(!(i >= n))
      {
        if(pool->end == pool->ptr)
        {
          return_value_poolGrow$1=poolGrow(pool);
          if(return_value_poolGrow$1 == 0)
            result = /*enum*/XML_ERROR_NO_MEMORY;

        }

        XML_Char *tmp_post$0=pool->ptr;
        pool->ptr = pool->ptr + 1l;
        *tmp_post$0 = buf[(signed long int)i];
        i = i + 1;
      }

      if(enc == parser->m_encoding)
        parser->m_eventPtr = entityTextPtr;

      result = /*enum*/XML_ERROR_INVALID_TOKEN;
      if(enc == parser->m_encoding)
        parser->m_eventPtr = next;

      result = /*enum*/XML_ERROR_INVALID_TOKEN;
    }

    if(enc == parser->m_encoding)
      parser->m_eventPtr = entityTextPtr;

    result = /*enum*/XML_ERROR_UNEXPECTED_STATE;
    entityTextPtr = next;
  }

endEntityValue:
  ;
  parser->m_prologState.inEntityValue = oldInEntityValue;
  return result;
}

// storeRawNames
// file xmlparse.c line 2559
static XML_Bool storeRawNames(XML_Parser parser)
{
  TAG *tag=parser->m_tagStack;
  while(!(tag == ((TAG *)NULL)))
  {
    signed int bufSize;
    signed int nameLen=(signed int)(sizeof(XML_Char) /*1ul*/  * (unsigned long int)(tag->name.strLen + 1));
    size_t rawNameLen;
    char *rawNameBuf=tag->buf + (signed long int)nameLen;
    if(tag->rawName == rawNameBuf)
      break;

    rawNameLen = (unsigned long int)tag->rawNameLength + (sizeof(XML_Char) /*1ul*/  - 1ul) & ~(sizeof(XML_Char) /*1ul*/  - 1ul);
    if(!(2147483647ul + -((unsigned long int)nameLen) >= rawNameLen))
      return 0;

    bufSize = nameLen + (signed int)rawNameLen;
    if(!(tag->bufEnd - tag->buf >= (signed long int)bufSize))
    {
      char *temp;
      void *return_value=parser->m_mem.realloc_fcn((void *)tag->buf, (size_t)bufSize);
      temp = (char *)return_value;
      if(temp == ((char *)NULL))
        return 0;

      if(tag->name.str == tag->buf)
        tag->name.str = (XML_Char *)temp;

      if(!(tag->name.localPart == ((const XML_Char *)NULL)))
        tag->name.localPart = (XML_Char *)temp + (tag->name.localPart - (XML_Char *)tag->buf);

      tag->buf = temp;
      tag->bufEnd = temp + (signed long int)bufSize;
      rawNameBuf = temp + (signed long int)nameLen;
    }

    memcpy((void *)rawNameBuf, (const void *)tag->rawName, (size_t)tag->rawNameLength);
    tag->rawName = rawNameBuf;
    tag = tag->parent;
  }
  return 1;
}

// testingAccountingGetCountBytesDirect
// file xmlparse.c line 7623
unsigned long long int testingAccountingGetCountBytesDirect(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return 0ull;

  else
    return parser->m_accounting.countBytesDirect;
}

// testingAccountingGetCountBytesIndirect
// file xmlparse.c line 7630
unsigned long long int testingAccountingGetCountBytesIndirect(XML_Parser parser)
{
  if(parser == ((XML_Parser)NULL))
    return 0ull;

  else
    return parser->m_accounting.countBytesIndirect;
}

// unsignedCharToPrintable
// file xmlparse.c line 7700
const char * unsignedCharToPrintable(unsigned char c)
{
  switch((signed int)c)
  {
    case 0:
      return "\\0";
    case 1:
      return "\\x1";
    case 2:
      return "\\x2";
    case 3:
      return "\\x3";
    case 4:
      return "\\x4";
    case 5:
      return "\\x5";
    case 6:
      return "\\x6";
    case 7:
      return "\\x7";
    case 8:
      return "\\x8";
    case 9:
      return "\\t";
    case 10:
      return "\\n";
    case 11:
      return "\\xB";
    case 12:
      return "\\xC";
    case 13:
      return "\\r";
    case 14:
      return "\\xE";
    case 15:
      return "\\xF";
    case 16:
      return "\\x10";
    case 17:
      return "\\x11";
    case 18:
      return "\\x12";
    case 19:
      return "\\x13";
    case 20:
      return "\\x14";
    case 21:
      return "\\x15";
    case 22:
      return "\\x16";
    case 23:
      return "\\x17";
    case 24:
      return "\\x18";
    case 25:
      return "\\x19";
    case 26:
      return "\\x1A";
    case 27:
      return "\\x1B";
    case 28:
      return "\\x1C";
    case 29:
      return "\\x1D";
    case 30:
      return "\\x1E";
    case 31:
      return "\\x1F";
    case 32:
      return " ";
    case 33:
      return "!";
    case 34:
      return "\\\"";
    case 35:
      return "#";
    case 36:
      return "$";
    case 37:
      return "%";
    case 38:
      return "&";
    case 39:
      return "'";
    case 40:
      return "(";
    case 41:
      return ")";
    case 42:
      return "*";
    case 43:
      return "+";
    case 44:
      return ",";
    case 45:
      return "-";
    case 46:
      return ".";
    case 47:
      return "/";
    case 48:
      return "0";
    case 49:
      return "1";
    case 50:
      return "2";
    case 51:
      return "3";
    case 52:
      return "4";
    case 53:
      return "5";
    case 54:
      return "6";
    case 55:
      return "7";
    case 56:
      return "8";
    case 57:
      return "9";
    case 58:
      return ":";
    case 59:
      return ";";
    case 60:
      return "<";
    case 61:
      return "=";
    case 62:
      return ">";
    case 63:
      return "?";
    case 64:
      return "@";
    case 65:
      return "A";
    case 66:
      return "B";
    case 67:
      return "C";
    case 68:
      return "D";
    case 69:
      return "E";
    case 70:
      return "F";
    case 71:
      return "G";
    case 72:
      return "H";
    case 73:
      return "I";
    case 74:
      return "J";
    case 75:
      return "K";
    case 76:
      return "L";
    case 77:
      return "M";
    case 78:
      return "N";
    case 79:
      return "O";
    case 80:
      return "P";
    case 81:
      return "Q";
    case 82:
      return "R";
    case 83:
      return "S";
    case 84:
      return "T";
    case 85:
      return "U";
    case 86:
      return "V";
    case 87:
      return "W";
    case 88:
      return "X";
    case 89:
      return "Y";
    case 90:
      return "Z";
    case 91:
      return "[";
    case 92:
      return "\\\\";
    case 93:
      return "]";
    case 94:
      return "^";
    case 95:
      return "_";
    case 96:
      return "`";
    case 97:
      return "a";
    case 98:
      return "b";
    case 99:
      return "c";
    case 100:
      return "d";
    case 101:
      return "e";
    case 102:
      return "f";
    case 103:
      return "g";
    case 104:
      return "h";
    case 105:
      return "i";
    case 106:
      return "j";
    case 107:
      return "k";
    case 108:
      return "l";
    case 109:
      return "m";
    case 110:
      return "n";
    case 111:
      return "o";
    case 112:
      return "p";
    case 113:
      return "q";
    case 114:
      return "r";
    case 115:
      return "s";
    case 116:
      return "t";
    case 117:
      return "u";
    case 118:
      return "v";
    case 119:
      return "w";
    case 120:
      return "x";
    case 121:
      return "y";
    case 122:
      return "z";
    case 123:
      return "{";
    case 124:
      return "|";
    case 125:
      return "}";
    case 126:
      return "~";
    case 127:
      return "\\x7F";
    case 128:
      return "\\x80";
    case 129:
      return "\\x81";
    case 130:
      return "\\x82";
    case 131:
      return "\\x83";
    case 132:
      return "\\x84";
    case 133:
      return "\\x85";
    case 134:
      return "\\x86";
    case 135:
      return "\\x87";
    case 136:
      return "\\x88";
    case 137:
      return "\\x89";
    case 138:
      return "\\x8A";
    case 139:
      return "\\x8B";
    case 140:
      return "\\x8C";
    case 141:
      return "\\x8D";
    case 142:
      return "\\x8E";
    case 143:
      return "\\x8F";
    case 144:
      return "\\x90";
    case 145:
      return "\\x91";
    case 146:
      return "\\x92";
    case 147:
      return "\\x93";
    case 148:
      return "\\x94";
    case 149:
      return "\\x95";
    case 150:
      return "\\x96";
    case 151:
      return "\\x97";
    case 152:
      return "\\x98";
    case 153:
      return "\\x99";
    case 154:
      return "\\x9A";
    case 155:
      return "\\x9B";
    case 156:
      return "\\x9C";
    case 157:
      return "\\x9D";
    case 158:
      return "\\x9E";
    case 159:
      return "\\x9F";
    case 160:
      return "\\xA0";
    case 161:
      return "\\xA1";
    case 162:
      return "\\xA2";
    case 163:
      return "\\xA3";
    case 164:
      return "\\xA4";
    case 165:
      return "\\xA5";
    case 166:
      return "\\xA6";
    case 167:
      return "\\xA7";
    case 168:
      return "\\xA8";
    case 169:
      return "\\xA9";
    case 170:
      return "\\xAA";
    case 171:
      return "\\xAB";
    case 172:
      return "\\xAC";
    case 173:
      return "\\xAD";
    case 174:
      return "\\xAE";
    case 175:
      return "\\xAF";
    case 176:
      return "\\xB0";
    case 177:
      return "\\xB1";
    case 178:
      return "\\xB2";
    case 179:
      return "\\xB3";
    case 180:
      return "\\xB4";
    case 181:
      return "\\xB5";
    case 182:
      return "\\xB6";
    case 183:
      return "\\xB7";
    case 184:
      return "\\xB8";
    case 185:
      return "\\xB9";
    case 186:
      return "\\xBA";
    case 187:
      return "\\xBB";
    case 188:
      return "\\xBC";
    case 189:
      return "\\xBD";
    case 190:
      return "\\xBE";
    case 191:
      return "\\xBF";
    case 192:
      return "\\xC0";
    case 193:
      return "\\xC1";
    case 194:
      return "\\xC2";
    case 195:
      return "\\xC3";
    case 196:
      return "\\xC4";
    case 197:
      return "\\xC5";
    case 198:
      return "\\xC6";
    case 199:
      return "\\xC7";
    case 200:
      return "\\xC8";
    case 201:
      return "\\xC9";
    case 202:
      return "\\xCA";
    case 203:
      return "\\xCB";
    case 204:
      return "\\xCC";
    case 205:
      return "\\xCD";
    case 206:
      return "\\xCE";
    case 207:
      return "\\xCF";
    case 208:
      return "\\xD0";
    case 209:
      return "\\xD1";
    case 210:
      return "\\xD2";
    case 211:
      return "\\xD3";
    case 212:
      return "\\xD4";
    case 213:
      return "\\xD5";
    case 214:
      return "\\xD6";
    case 215:
      return "\\xD7";
    case 216:
      return "\\xD8";
    case 217:
      return "\\xD9";
    case 218:
      return "\\xDA";
    case 219:
      return "\\xDB";
    case 220:
      return "\\xDC";
    case 221:
      return "\\xDD";
    case 222:
      return "\\xDE";
    case 223:
      return "\\xDF";
    case 224:
      return "\\xE0";
    case 225:
      return "\\xE1";
    case 226:
      return "\\xE2";
    case 227:
      return "\\xE3";
    case 228:
      return "\\xE4";
    case 229:
      return "\\xE5";
    case 230:
      return "\\xE6";
    case 231:
      return "\\xE7";
    case 232:
      return "\\xE8";
    case 233:
      return "\\xE9";
    case 234:
      return "\\xEA";
    case 235:
      return "\\xEB";
    case 236:
      return "\\xEC";
    case 237:
      return "\\xED";
    case 238:
      return "\\xEE";
    case 239:
      return "\\xEF";
    case 240:
      return "\\xF0";
    case 241:
      return "\\xF1";
    case 242:
      return "\\xF2";
    case 243:
      return "\\xF3";
    case 244:
      return "\\xF4";
    case 245:
      return "\\xF5";
    case 246:
      return "\\xF6";
    case 247:
      return "\\xF7";
    case 248:
      return "\\xF8";
    case 249:
      return "\\xF9";
    case 250:
      return "\\xFA";
    case 251:
      return "\\xFB";
    case 252:
      return "\\xFC";
    case 253:
      return "\\xFD";
    case 254:
      return "\\xFE";
    case 255:
      return "\\xFF";
    default:
    {
      (void)sizeof(signed int) /*4ul*/ ;
      /* assertion 0 */
      assert(0 != 0);
      return "dead code";
    }
  }
  (void)sizeof(signed int) /*4ul*/ ;
  /* assertion 0 */
  assert(0 != 0);
}

