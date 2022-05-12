// direct change: a/libusb/core.c:1702:18:libusb_release_interface() -> b/libusb/core.c:1703:18:libusb_release_interface()
#ifdef CBMC
#include <assert.h>
#include <features.h>
#include <features-time64.h>
#include <stdc-predef.h>
#include <sys/cdefs.h>
#include <gnu/stubs.h>
#include <gnu/stubs-64.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>
#include <endian.h>
#include <sys/select.h>
#include <alloca.h>
#include <sys/time.h>
#include <limits.h>
#include <linux/limits.h>
#include <time.h>
#include <poll.h>
#include <sys/poll.h>
#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <string.h>
#include <strings.h>


#include "libusb/libusbi.h"
#include "config.h"
#include "libusb/libusb.h"
#include "libusb/os/events_posix.h"
#include "libusb/os/threads_posix.h"
#include "libusb/version.h"
#include "libusb/version_nano.h"

struct libusb_device_handle nondet_libusb_device_handle();
int nondet_int();

int libusb_release_interface_old_b026324c6904b2a(struct libusb_device_handle* dev_handle, int interface_number);
int libusb_release_interface(struct libusb_device_handle* dev_handle, int interface_number);

void euf_main() {
  struct libusb_device_handle* dev_handle;
  *dev_handle = nondet_libusb_device_handle();
  int interface_number = nondet_int();

  __CPROVER_assume(
    interface_number == 0
  );

  int ret_old = libusb_release_interface_old_b026324c6904b2a(dev_handle, interface_number);
  int ret = libusb_release_interface(dev_handle, interface_number);

  __CPROVER_assert(ret_old == ret, "Equivalent output");

}
#endif
