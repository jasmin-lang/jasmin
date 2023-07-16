#include <stdio.h>
#include <stdint.h>
struct asm_state {
    int64_t rax;
    int64_t rcx;
    int64_t rdx;
    int64_t rbx;
    int64_t rsp;        // should be dummy and ignored
    int64_t rbp;
    int64_t rsi;
    int64_t rdi;
    int64_t r8;
    int64_t r9;
    int64_t r10;
    int64_t r11;
    int64_t r12;
    int64_t r13;
    int64_t r14;
    int64_t r15;
    // RFLAGS
    int64_t rflags;
};

extern void set_execute_get(struct asm_state *);

void set_execute_get_wrapper(struct asm_state *state) {
    set_execute_get(state);
    printf("the flag is %ld\n", state->rflags);
}