// 'P_' is a macro, clang will expand macros automatically but we need to actually include them in the TU
// for this to work. The same goes for custom types like 'onig_posix_regmatch_t'
// To resolve this issue we need to have the #includes still available in each TU
#ifndef P_
#if defined(__STDC__) || defined(_WIN32)
# define P_(args) args
#else
# define P_(args) ()
#endif
#endif

#define ONIG_EXTERN   extern

ONIG_EXTERN int    onig_posix_regcomp P_((onig_posix_regex_t* reg, const char* pat, int options));
ONIG_EXTERN int    onig_posix_regexec P_((onig_posix_regex_t* reg, const char* str, size_t nmatch, onig_posix_regmatch_t* matches, int options
));
ONIG_EXTERN void   onig_posix_regfree P_((onig_posix_regex_t* reg));
ONIG_EXTERN size_t onig_posix_regerror P_((int code, const onig_posix_regex_t* reg, char* buf, size_t size));
ONIG_EXTERN int    regcomp P_((regex_t* reg, const char* pat, int options));
ONIG_EXTERN int    regexec P_((regex_t* reg, const char* str, size_t nmatch, regmatch_t* matches, int options));
ONIG_EXTERN void   regfree P_((regex_t* reg));
ONIG_EXTERN size_t regerror P_((int code, const regex_t* reg, char* buf, size_t size));


extern int    onig_strncmp P_((const UChar* s1, const UChar* s2, int n));
extern void   onig_strcpy P_((UChar* dest, const UChar* src, const UChar* end));
extern void   onig_scan_env_set_error_string P_((ParseEnv* env, int ecode, UChar* arg, UChar* arg_end));
extern int    onig_reduce_nested_quantifier P_((Node* pnode));
extern int    onig_node_copy(Node** rcopy, Node* from);
extern int    onig_node_str_cat P_((Node* node, const UChar* s, const UChar* end));
extern int    onig_node_str_set P_((Node* node, const UChar* s, const UChar* end, int need_free));
extern void   onig_node_str_clear P_((Node* node, int need_free));
extern void   onig_node_free P_((Node* node));
extern int    onig_node_reset_empty P_((Node* node));
extern int    onig_node_reset_fail P_((Node* node));
extern Node*  onig_node_new_bag P_((enum BagType type));
extern Node*  onig_node_new_str P_((const UChar* s, const UChar* end));
extern Node*  onig_node_new_list P_((Node* left, Node* right));
extern Node*  onig_node_new_alt P_((Node* left, Node* right));
extern int    onig_names_free P_((regex_t* reg));
extern int    onig_parse_tree P_((Node** root, const UChar* pattern, const UChar* end, regex_t* reg, ParseEnv* env));
extern int    onig_free_shared_cclass_table P_((void));
extern int    onig_is_code_in_cc P_((OnigEncoding enc, OnigCodePoint code, CClassNode* cc));
extern int    onig_new_cclass_with_code_list(Node** rnode, OnigEncoding enc, int n, OnigCodePoint codes[]);
extern OnigLen onig_get_tiny_min_len(Node* node, unsigned int inhibit_node_types, int* invalid_node);

