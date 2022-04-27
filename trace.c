#include <stdio.h>
#include <stdlib.h>
#define __USE_GNU
#include <dlfcn.h>

FILE* fp_trace;

void __attribute__ ((no_instrument_function,constructor))
trace_begin (void) {
  //char* logfile = getenv("TRACE_LOGFILE");
  const char* logfile="/tmp/jq_trace";
  if (logfile != NULL) {
    fp_trace = fopen(logfile, "w");
  }
}
 
void __attribute__ ((no_instrument_function,destructor))
trace_end (void) {
  if (fp_trace != NULL) {
    fclose(fp_trace);
  }
}

void __attribute__((no_instrument_function))
__cyg_profile_func_enter (void *this_fn, void *call_site) {
  Dl_info info;
  dladdr(this_fn, &info);
  fprintf(fp_trace, "[Enter] %s\n", info.dli_sname);
}

void __attribute__((no_instrument_function))
__cyg_profile_func_exit(void *this_fn, void *call_site) {
  /* empty */
}

#undef __USE_GNU

