
#include "jasmin_syscall.h"

#if defined(__linux__) 

#include <unistd.h>
#include <stdint.h>
#include <sys/random.h>

uint8_t* __jasmin_syscall_randombytes__(uint8_t* _x, uint64_t xlen)
{
  int i;
  uint8_t* x = _x;

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

  return _x;
}

#endif

#if defined(__APPLE__)

#include <stdlib.h>

#if !(defined(__MAC_OS_X_VERSION_MIN_REQUIRED) && __MAC_OS_X_VERSION_MIN_REQUIRED >= 101200)
#error "macOS version not supported (>= 10.12)"
#endif

uint8_t* __jasmin_syscall_randombytes__(uint8_t* x, uint64_t xlen){
  arc4random_buf(x, xlen);
  return x;
}

#endif
