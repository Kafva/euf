ONIG_EXTERN int    onig_posix_regcomp P_((onig_posix_regex_t* reg, const char* pat, int options));
ONIG_EXTERN int    onig_posix_regexec P_((onig_posix_regex_t* reg, const char* str, size_t nmatch, onig_posix_regmatch_t* matches, int options
));
ONIG_EXTERN void   onig_posix_regfree P_((onig_posix_regex_t* reg));
ONIG_EXTERN size_t onig_posix_regerror P_((int code, const onig_posix_regex_t* reg, char* buf, size_t size));
ONIG_EXTERN int    regcomp P_((regex_t* reg, const char* pat, int options));
ONIG_EXTERN int    regexec P_((regex_t* reg, const char* str, size_t nmatch, regmatch_t* matches, int options));
ONIG_EXTERN void   regfree P_((regex_t* reg));
ONIG_EXTERN size_t regerror P_((int code, const regex_t* reg, char* buf, size_t size));
