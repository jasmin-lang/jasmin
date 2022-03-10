#include <stdint.h>
#ifndef JASMIN_SYSCALL
#define JASMIN_SYSCALL
/* FIXME this need xlen to be Uptr */
unsigned char * __jasmin_syscall_randombytes__(unsigned char *x, uint64_t xlen)
asm("__jasmin_syscall_randombytes__");

#endif
