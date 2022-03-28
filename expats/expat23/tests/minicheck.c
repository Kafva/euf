/* Miniature re-implementation of the "check" library.

   This is intended to support just enough of check to run the Expat
   tests.  This interface is based entirely on the portion of the
   check library being used.
                            __  __            _
                         ___\ \/ /_ __   __ _| |_
                        / _ \\  /| '_ \ / _` | __|
                       |  __//  \| |_) | (_| | |_
                        \___/_/\_\ .__/ \__,_|\__|
                                 |_| XML parser

   Copyright (c) 2004-2006 Fred L. Drake, Jr. <fdrake@users.sourceforge.net>
   Copyright (c) 2016-2020 Sebastian Pipping <sebastian@pipping.org>
   Copyright (c) 2017      Rhodri James <rhodri@wildebeest.org.uk>
   Copyright (c) 2018      Marco Maggi <marco.maggi-ipsu@poste.it>
   Copyright (c) 2019      David Loffredo <loffredo@steptools.com>
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

#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <assert.h>
#include <string.h>

#include "internal.h" /* for UNUSED_P only */
#include "minicheck.h"

Suite *
suite_create_old_b026324c6904b2a(const char *name) {
  Suite *suite = (Suite *)calloc(1, sizeof(Suite));
  if (suite != NULL) {
    suite->name = name;
  }
  return suite;
}

TCase *
tcase_create_old_b026324c6904b2a(const char *name) {
  TCase *tc = (TCase *)calloc(1, sizeof(TCase));
  if (tc != NULL) {
    tc->name = name;
  }
  return tc;
}

void
suite_add_tcase_old_b026324c6904b2a(Suite *suite, TCase *tc) {
  assert(suite != NULL);
  assert(tc != NULL);
  assert(tc->next_tcase == NULL);

  tc->next_tcase = suite->tests;
  suite->tests = tc;
}

void
tcase_add_checked_fixture_old_b026324c6904b2a(TCase *tc, tcase_setup_function setup,
                          tcase_teardown_function teardown) {
  assert(tc != NULL);
  tc->setup = setup;
  tc->teardown = teardown;
}

void
tcase_add_test_old_b026324c6904b2a(TCase *tc, tcase_test_function test) {
  assert(tc != NULL);
  if (tc->allocated == tc->ntests) {
    int nalloc = tc->allocated + 100;
    size_t new_size = sizeof(tcase_test_function) * nalloc;
    tcase_test_function *new_tests = realloc(tc->tests, new_size);
    assert(new_tests != NULL);
    tc->tests = new_tests;
    tc->allocated = nalloc;
  }
  tc->tests[tc->ntests] = test;
  tc->ntests++;
}

static void
tcase_free_old_b026324c6904b2a(TCase *tc) {
  if (! tc) {
    return;
  }

  free(tc->tests);
  free(tc);
}

static void
suite_free_old_b026324c6904b2a(Suite *suite) {
  if (! suite) {
    return;
  }

  while (suite->tests != NULL) {
    TCase *next = suite->tests->next_tcase;
    tcase_free_old_b026324c6904b2a(suite->tests);
    suite->tests = next;
  }
  free(suite);
}

SRunner *
srunner_create_old_b026324c6904b2a(Suite *suite) {
  SRunner *runner = calloc(1, sizeof(SRunner));
  if (runner != NULL) {
    runner->suite = suite;
  }
  return runner;
}

static jmp_buf env;

static char const *_check_current_function = NULL;
static int _check_current_lineno = -1;
static char const *_check_current_filename = NULL;

void
_check_set_test_info_old_b026324c6904b2a(char const *function, char const *filename, int lineno) {
  _check_current_function = function;
  _check_current_lineno = lineno;
  _check_current_filename = filename;
}

static void
handle_success_old_b026324c6904b2a(int verbosity) {
  if (verbosity >= CK_VERBOSE) {
    printf("PASS: %s\n", _check_current_function);
  }
}

static void
handle_failure_old_b026324c6904b2a(SRunner *runner, int verbosity, const char *phase_info) {
  runner->nfailures++;
  if (verbosity != CK_SILENT) {
    printf("FAIL: %s (%s at %s:%d)\n", _check_current_function, phase_info,
           _check_current_filename, _check_current_lineno);
  }
}

void
srunner_run_all_old_b026324c6904b2a(SRunner *runner, int verbosity) {
  Suite *suite;
  TCase *volatile tc;
  assert(runner != NULL);
  suite = runner->suite;
  tc = suite->tests;
  while (tc != NULL) {
    volatile int i;
    for (i = 0; i < tc->ntests; ++i) {
      runner->nchecks++;

      if (tc->setup != NULL) {
        /* setup */
        if (setjmp(env)) {
          handle_failure_old_b026324c6904b2a(runner, verbosity, "during setup");
          continue;
        }
        tc->setup();
      }
      /* test */
      if (setjmp(env)) {
        handle_failure_old_b026324c6904b2a(runner, verbosity, "during actual test");
        continue;
      }
      (tc->tests[i])();

      /* teardown */
      if (tc->teardown != NULL) {
        if (setjmp(env)) {
          handle_failure_old_b026324c6904b2a(runner, verbosity, "during teardown");
          continue;
        }
        tc->teardown();
      }

      handle_success_old_b026324c6904b2a(verbosity);
    }
    tc = tc->next_tcase;
  }
  if (verbosity != CK_SILENT) {
    int passed = runner->nchecks - runner->nfailures;
    double percentage = ((double)passed) / runner->nchecks;
    int display = (int)(percentage * 100);
    printf("%d%%: Checks: %d, Failed: %d\n", display, runner->nchecks,
           runner->nfailures);
  }
}

void
_fail_unless(int condition, const char *file, int line, const char *msg) {
  /* Always print the error message so it isn't lost.  In this case,
     we have a failure, so there's no reason to be quiet about what
     it is.
  */
  UNUSED_P(condition);
  _check_current_filename = file;
  _check_current_lineno = line;
  if (msg != NULL) {
    const int has_newline = (msg[strlen(msg) - 1] == '\n');
    fprintf(stderr, "ERROR: %s%s", msg, has_newline ? "" : "\n");
  }
  longjmp(env, 1);
}

int
srunner_ntests_failed_old_b026324c6904b2a(SRunner *runner) {
  assert(runner != NULL);
  return runner->nfailures;
}

void
srunner_free_old_b026324c6904b2a(SRunner *runner) {
  if (! runner) {
    return;
  }

  suite_free_old_b026324c6904b2a(runner->suite);
  free(runner);
}
