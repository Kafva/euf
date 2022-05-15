#include "regparse.h"
#include "st.h"

// Using a static header with struct definitions in this manner is bound to
// cause undesirable consequences in updates where the struct definitions
// differ. Limiting the update range to ~1 year aids somewhat in reducing the
// impact of this issue.

#ifdef USE_ST_LIBRARY

typedef struct {
  UChar* s;
  UChar* end;
} st_str_end_key;

typedef st_table  NameTable;
typedef st_data_t HashDataType;   /* 1.6 st.h doesn't define st_data_t type */

// Required for: callout_name_table_hash() in
//    tests/configs/libonig_b99e70d9_153974cf.json
typedef struct {
  OnigEncoding enc;
  int    type; // callout type: single or not
  UChar* s;
  UChar* end;
} st_callout_name_key;

#else

typedef struct {
  NameEntry* e;
  int        num;
  int        alloc;
} NameTable;

#endif

// Required for: callout_func_list_add() in
//    tests/configs/libonig_b99e70d9_153974cf.json
#ifdef USE_CALLOUT
typedef struct {
  OnigCalloutType type;
  int             in;
  OnigCalloutFunc start_func;
  OnigCalloutFunc end_func;
  int             arg_num;
  int             opt_arg_num;
  OnigType        arg_types[ONIG_CALLOUT_MAX_ARG_NUM];
  OnigValue       opt_defaults[ONIG_CALLOUT_MAX_ARG_NUM];
  UChar*          name; /* reference to GlobalCalloutNameTable entry: e->name */
} CalloutNameListEntry;

typedef struct {
  int  n;
  int  alloc;
  CalloutNameListEntry* v;
} CalloutNameListType;
#endif

typedef struct {
  UChar* name;
  int    name_len;   /* byte length */
  int    back_num;   /* number of backrefs */
  int    back_alloc;
  int    back_ref1;
  int*   back_refs;
} NameEntry;


typedef struct {
  int (*func)(const UChar*, const UChar*,int,int*,regex_t*,void*);
  regex_t* reg;
  void* arg;
  int ret;
  OnigEncoding enc;
} INamesArg;


enum TokenSyms {
  TK_EOT      = 0,   /* end of token */
  TK_RAW_BYTE = 1,
  TK_CHAR,
  TK_STRING,
  TK_CODE_POINT,
  TK_ANYCHAR,
  TK_CHAR_TYPE,
  TK_BACKREF,
  TK_CALL,
  TK_ANCHOR,
  TK_OP_REPEAT,
  TK_INTERVAL,
  TK_ANYCHAR_ANYTIME,  /* SQL '%' == .* */
  TK_ALT,
  TK_SUBEXP_OPEN,
  TK_SUBEXP_CLOSE,
  TK_CC_OPEN,
  TK_QUOTE_OPEN,
  TK_CHAR_PROPERTY,    /* \p{...}, \P{...} */
  /* in cc */
  TK_CC_CLOSE,
  TK_CC_RANGE,
  TK_POSIX_BRACKET_OPEN,
  TK_CC_AND,             /* && */
  TK_CC_CC_OPEN          /* [ */
};

typedef struct {
  enum TokenSyms type;
  int escaped;
  int base;   /* is number: 8, 16 (used in [....]) */
  UChar* backp;
  union {
    UChar* s;
    int   c;
    OnigCodePoint code;
    int   anchor;
    int   subtype;
    struct {
      int lower;
      int upper;
      int greedy;
      int possessive;
    } repeat;
    struct {
      int  num;
      int  ref1;
      int* refs;
      int  by_name;
#ifdef USE_BACKREF_WITH_LEVEL
      int  exist_level;
      int  level;   /* \k<name+n> */
#endif
    } backref;
    struct {
      UChar* name;
      UChar* name_end;
      int    gnum;
    } call;
    struct {
      int ctype;
      int not;
    } prop;
  } u;
} OnigToken;

typedef struct {
  ScanEnv*    env;
  CClassNode* cc;
  Node*       alt_root;
  Node**      ptail;
} IApplyCaseFoldArg;

