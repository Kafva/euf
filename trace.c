#include <stdio.h>
#include <stdlib.h>
#include <time.h>

FILE* fp_trace;

void __attribute__ ((no_instrument_function,constructor))
trace_begin (void) {
  char* logfile = getenv("TRACE_LOGFILE");
  if (logfile == NULL) {
    logfile = "/tmp/FALLBACK_LOG";
  }
  fp_trace = fopen(logfile, "w");
}
 
void __attribute__ ((no_instrument_function,destructor))
trace_end (void) {
  if (fp_trace != NULL) {
    fclose(fp_trace);
  }
}

void __attribute__((no_instrument_function))
__cyg_profile_func_enter(void *this_fn, void *call_site) {
  if (fp_trace != NULL) {
    fprintf(fp_trace, "e %p %p %lu\n", this_fn, call_site, time(NULL));
  }
}

void __attribute__((no_instrument_function))
__cyg_profile_func_exit(void *this_fn, void *call_site) {
  /* empty */
}

#undef __USE_GNU

