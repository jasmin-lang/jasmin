#include <stdint.h>

struct asm_state {
    uint64_t rax;
    uint64_t rcx;
    uint64_t rdx;
    uint64_t rbx;
    uint64_t rsi;
    uint64_t rdi;
    uint64_t rsp;       // should be dummy and ignored for now
    uint64_t rbp;
    uint64_t r8;
    uint64_t r9;
    uint64_t r10;
    uint64_t r11;
    uint64_t r12;
    uint64_t r13;
    uint64_t r14;
    uint64_t r15;
    // RFLAGS
    uint64_t rflags;
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
