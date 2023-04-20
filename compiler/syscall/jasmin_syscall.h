#include <stdint.h>
#ifndef JASMIN_SYSCALL
#define JASMIN_SYSCALL
/* FIXME this need xlen to be Uptr */
uint8_t* __jasmin_syscall_randombytes__(uint8_t* x, uint64_t xlen)
asm("__jasmin_syscall_randombytes__");

#endif
