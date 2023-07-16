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
    printf("Post Execution\n");
    printf("rax = %ld\n", state->rax);
    printf("rcx = %ld\n", state->rcx);
    printf("rdx = %ld\n", state->rdx);
    printf("rbx = %ld\n", state->rbx);
    printf("rsp = %ld\n", state->rsp);
    printf("rbp = %ld\n", state->rbp);
    printf("rsi = %ld\n", state->rsi);
    printf("rdi = %ld\n", state->rdi);
    printf("r8 = %ld\n", state->r8);
    printf("r9 = %ld\n", state->r9);
    printf("r10 = %ld\n", state->r10);
    printf("r11 = %ld\n", state->r11);
    printf("r12 = %ld\n", state->r12);
    printf("r13 = %ld\n", state->r13);
    printf("r14 = %ld\n", state->r14);
    printf("r15 = %ld\n", state->r15);
    printf("rflags = %ld\n", state->rflags);
}
