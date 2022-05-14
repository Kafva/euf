#include "oniguruma.h"
#include "regparse.h"

#define REPEAT_RANGE_ALLOC  4
#define QUANTIFIER_EXPAND_LIMIT_SIZE   50
#define CKN_ON   (ckn > 0)
#define GET_CHAR_LEN_VARLEN           -1
#define GET_CHAR_LEN_TOP_ALT_VARLEN   -2
#define RECURSION_EXIST       1
#define RECURSION_INFINITE    2
#define FOUND_CALLED_NODE    1
#define THRESHOLD_CASE_FOLD_ALT_FOR_EXPANSION  8
#define CEC_THRES_NUM_BIG_REPEAT         512
#define CEC_INFINITE_NUM          0x7fffffff
#define CEC_IN_INFINITE_REPEAT    (1<<0)
#define CEC_IN_FINITE_REPEAT      (1<<1)
#define CEC_CONT_BIG_REPEAT       (1<<2)
#define IN_ALT        (1<<0)
#define IN_NOT        (1<<1)
#define IN_REPEAT     (1<<2)
#define IN_VAR_REPEAT (1<<3)
#define IN_CALL       (1<<4)
#define IN_RECCALL    (1<<5)
#define EXPAND_STRING_MAX_LENGTH  100
#define ALLOWED_ENCLOSE_IN_LB       ( ENCLOSE_MEMORY | ENCLOSE_OPTION )
#define ALLOWED_ENCLOSE_IN_LB_NOT   ENCLOSE_OPTION
#define OPT_EXACT_MAXLEN   24
#define COMP_EM_BASE  20
#define MAX_NODE_OPT_INFO_REF_COUNT    5
#define COMPILE_INIT_SIZE  20
#define ARG_SPECIAL     -1
#define ARG_NON          0
#define ARG_RELADDR      1
#define ARG_ABSADDR      2
#define ARG_LENGTH       3
#define ARG_MEMNUM       4
#define ARG_OPTION       5
#define ARG_STATE_CHECK  6

typedef struct {
  OnigLen min;  /* min byte length */
  OnigLen max;  /* max byte length */
} MinMaxLen;

typedef struct {
  MinMaxLen        mmd;
  OnigEncoding     enc;
  OnigOptionType   options;
  OnigCaseFoldType case_fold_flag;
  ScanEnv*         scan_env;
} OptEnv;

typedef struct {
  int left_anchor;
  int right_anchor;
} OptAncInfo;

typedef struct {
  MinMaxLen  mmd; /* info position */
  OptAncInfo anc;

  int   reach_end;
  int   ignore_case;
  int   len;
  UChar s[OPT_EXACT_MAXLEN];
} OptExactInfo;

typedef struct {
  MinMaxLen mmd; /* info position */
  OptAncInfo anc;

  int   value;      /* weighted value */
  UChar map[ONIG_CHAR_TABLE_SIZE];
} OptMapInfo;

typedef struct {
  MinMaxLen    len;

  OptAncInfo   anc;
  OptExactInfo exb;    /* boundary */
  OptExactInfo exm;    /* middle */
  OptExactInfo expr;   /* prec read (?=...) */

  OptMapInfo   map;   /* boundary */
} NodeOptInfo;

// Failed analysis for optimize_node() without this in:
//  ./tests/configs/libonig_07005064_eed90744.json 
typedef NodeOptInfo NodeOpt;
