
#include "jasmin_syscall.h"

#if defined(__linux__) 

#include <unistd.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <stdio.h>
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

uint64_t __jasmin_syscall_open__(uint8_t* x, uint64_t xlen)
{
  uint8_t filename[xlen + 1];
  memcpy(filename, x, xlen);
  filename[xlen] = 0;

  return (uint64_t)open(filename, O_RDWR|O_CREAT, S_IRUSR|S_IWUSR);
}

uint8_t __jasmin_syscall_close__(uint64_t fd)
{
  int success = close(fd);

  if (success == 0) {
    return 1;
  } else {
    return 0;
  }
}

uint8_t* __jasmin_syscall_write__(uint8_t* _x, uint64_t xlen, uint64_t fd)
{
  size_t i;
  uint8_t* x = _x;

  while (xlen > 0) {
    i = write(fd, x, xlen);
    if (i < 1) {
      continue;
    }
    x += i;
    xlen -= i;
  }

  return _x;
}

uint8_t* __jasmin_syscall_read__(uint8_t* _x, uint64_t xlen, uint64_t fd)
{
  size_t i;
  uint8_t* x = _x;

  i = read(fd, x, xlen);
  if (i < 1) {
    // Do something
      perror("Something went wrong while reading the file");
  }
  x += i;
  xlen -= i;

  memset(x, 0, xlen);

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
