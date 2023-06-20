#include <stdint.h>

struct asm_state {
    int64_t rax;
    int64_t rcx;
    int64_t rdx;
    int64_t rbx;
    int64_t rsp;       // should be dummy and ignored for now
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

void increment_rax (struct asm_state* state) {
    state->rax += 1;
    if (state->rax == 100) {        // Synthetic bug
        state->rax = 0;
    }
}

void sub_rbx_from_rax(struct asm_state* state) {
    if (state->rax == 5) {              // Creating a bug here
        state->rax = 5;
    }
    if (state->rax >= state->rbx) {
        state->rax -= state->rbx;
    }
}
