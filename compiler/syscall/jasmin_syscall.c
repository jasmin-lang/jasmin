
#include "jasmin_syscall.h"

#if defined(__linux__) 

#include <unistd.h>
#include <stdint.h>
#include <sys/random.h>

unsigned char * __jasmin_syscall_randombytes__(unsigned char *x, uint64_t xlen)
{

  int i;

  while (xlen > 0) {
    if (xlen < 1048576) i = xlen; else i = 1048576;

    i = getrandom(x,i,0);
    if (i < 1) {
      sleep(1);
      continue;
    }
    x += i;
    xlen -= i;
  }
  return x;
}

#endif

#if defined(__APPLE__)

#include <stdlib.h>

#if !(defined(__MAC_OS_X_VERSION_MIN_REQUIRED) && __MAC_OS_X_VERSION_MIN_REQUIRED >= 101200)
#error "macOS version not supported (>= 10.12)"
#endif

unsigned char * __jasmin_syscall_randombytes__(unsigned char *p, uint64_t plen){
  arc4random_buf(p, plen);
  return p;
}

#endif
