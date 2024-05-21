#include <stdint.h>
#ifndef JASMIN_SYSCALL
#define JASMIN_SYSCALL
/* FIXME this need xlen to be Uptr */
uint8_t* __jasmin_syscall_randombytes__(uint8_t* x, uint64_t xlen)
asm("__jasmin_syscall_randombytes__");

uint64_t __jasmin_syscall_open__(uint8_t* x, uint64_t xlen)
asm("__jasmin_syscall_open__");

uint8_t __jasmin_syscall_close__(uint64_t fd)
asm("__jasmin_syscall_close__");

uint8_t* __jasmin_syscall_write__(uint8_t* x, uint64_t xlen, uint64_t fd)
asm("__jasmin_syscall_write__");

uint8_t* __jasmin_syscall_read__(uint8_t* x, uint64_t xlen, uint64_t fd)
asm("__jasmin_syscall_read__");

#endif
