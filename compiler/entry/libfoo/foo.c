#include <stdio.h>
#include <stdint.h>
#include <keystone/keystone.h>
#include <unicorn/unicorn.h>

// memory address where emulation starts
#define ADDRESS 0x1000000

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

    // XMM registers (TODO: should change from 64 bit to 128/256 bits
    // later)
    int64_t xmm0_0;
    int64_t xmm0_1;
    int64_t xmm0_2;
    int64_t xmm0_3;

    int64_t xmm1_0;
    int64_t xmm1_1;
    int64_t xmm1_2;
    int64_t xmm1_3;

    int64_t xmm2_0;
    int64_t xmm2_1;
    int64_t xmm2_2;
    int64_t xmm2_3;

    int64_t xmm3_0;
    int64_t xmm3_1;
    int64_t xmm3_2;
    int64_t xmm3_3;

    int64_t xmm4_0;
    int64_t xmm4_1;
    int64_t xmm4_2;
    int64_t xmm4_3;

    int64_t xmm5_0;
    int64_t xmm5_1;
    int64_t xmm5_2;
    int64_t xmm5_3;

    int64_t xmm6_0;
    int64_t xmm6_1;
    int64_t xmm6_2;
    int64_t xmm6_3;

    int64_t xmm7_0;
    int64_t xmm7_1;
    int64_t xmm7_2;
    int64_t xmm7_3;

    int64_t xmm8_0;
    int64_t xmm8_1;
    int64_t xmm8_2;
    int64_t xmm8_3;


    int64_t xmm9_0;
    int64_t xmm9_1;
    int64_t xmm9_2;
    int64_t xmm9_3;

    int64_t xmm10_0;
    int64_t xmm10_1;
    int64_t xmm10_2;
    int64_t xmm10_3;

    int64_t xmm11_0;
    int64_t xmm11_1;
    int64_t xmm11_2;
    int64_t xmm11_3;

    int64_t xmm12_0;
    int64_t xmm12_1;
    int64_t xmm12_2;
    int64_t xmm12_3;

    int64_t xmm13_0;
    int64_t xmm13_1;
    int64_t xmm13_2;
    int64_t xmm13_3;

    int64_t xmm14_0;
    int64_t xmm14_1;
    int64_t xmm14_2;
    int64_t xmm14_3;

    int64_t xmm15_0;
    int64_t xmm15_1;
    int64_t xmm15_2;
    int64_t xmm15_3;

    // RFLAGS
    int64_t rflags;
};

extern void set_execute_get(struct asm_state *);

void set_execute_get_wrapper(struct asm_state *state) {
    set_execute_get(state);
    printf("Post Execution\n");
    printf("rax = %lx\n", state->rax);
    printf("rcx = %lx\n", state->rcx);
    printf("rdx = %lx\n", state->rdx);
    printf("rbx = %lx\n", state->rbx);
    printf("rsp = %lx\n", state->rsp);
    printf("rbp = %lx\n", state->rbp);
    printf("rsi = %lx\n", state->rsi);
    printf("rdi = %lx\n", state->rdi);
    printf("r8 = %lx\n", state->r8);
    printf("r9 = %lx\n", state->r9);
    printf("r10 = %lx\n", state->r10);
    printf("r11 = %lx\n", state->r11);
    printf("r12 = %lx\n", state->r12);
    printf("r13 = %lx\n", state->r13);
    printf("r14 = %lx\n", state->r14);
    printf("r15 = %lx\n", state->r15);
    printf("xmm0 = %lx %lx %lx %lx \n", state->xmm0_3, state->xmm0_2, state->xmm0_1, state->xmm0_0);
    printf("xmm1 = %lx %lx %lx %lx \n", state->xmm1_3, state->xmm1_2, state->xmm1_1, state->xmm1_0);
    printf("xmm2 = %lx %lx %lx %lx \n", state->xmm2_3, state->xmm2_2, state->xmm2_1, state->xmm2_0);
    printf("xmm3 = %lx %lx %lx %lx \n", state->xmm3_3, state->xmm3_2, state->xmm3_1, state->xmm3_0);
    printf("xmm4 = %lx %lx %lx %lx \n", state->xmm4_3, state->xmm4_2, state->xmm4_1, state->xmm4_0);
    printf("xmm5 = %lx %lx %lx %lx \n", state->xmm5_3, state->xmm5_2, state->xmm5_1, state->xmm5_0);
    printf("xmm6 = %lx %lx %lx %lx \n", state->xmm6_3, state->xmm6_2, state->xmm6_1, state->xmm6_0);
    printf("xmm7 = %lx %lx %lx %lx \n", state->xmm7_3, state->xmm7_2, state->xmm7_1, state->xmm7_0);
    printf("xmm8 = %lx %lx %lx %lx \n", state->xmm8_3, state->xmm8_2, state->xmm8_1, state->xmm8_0);
    printf("xmm9 = %lx %lx %lx %lx \n", state->xmm9_3, state->xmm9_2, state->xmm9_1, state->xmm9_0);
    printf("xmm10 = %lx %lx %lx %lx \n", state->xmm10_3, state->xmm10_2, state->xmm10_1, state->xmm10_0);
    printf("xmm11 = %lx %lx %lx %lx \n", state->xmm11_3, state->xmm11_2, state->xmm11_1, state->xmm11_0);
    printf("xmm12 = %lx %lx %lx %lx \n", state->xmm12_3, state->xmm12_2, state->xmm12_1, state->xmm12_0);
    printf("xmm13 = %lx %lx %lx %lx \n", state->xmm13_3, state->xmm13_2, state->xmm13_1, state->xmm13_0);
    printf("xmm14 = %lx %lx %lx %lx \n", state->xmm14_3, state->xmm14_2, state->xmm14_1, state->xmm14_0);
    printf("xmm15 = %lx %lx %lx %lx \n", state->xmm15_3, state->xmm15_2, state->xmm15_1, state->xmm15_0);
    printf("rflags = %lx\n", state->rflags);
}

/*
void set_execute_get_emulator(struct asm_state *state) {

    // NOT the best.. please forgive
    FILE* fd = NULL;
    char asm_instr[26] = {0};

    // Keystone Stuff
    ks_engine *ks;
    ks_err k_err;
    size_t count;
    size_t size;
    unsigned char *encode;

    // Unicorn Stuff
    uc_engine *uc;
    uc_err err;

    fd = fopen("asm_instr.txt", "r");
    if (NULL == fd) {
        printf("File asm_instr.txt cannot be opened\n");
        return;
    } else {
        if (fgets(asm_instr, 26, fd) == NULL) {
            printf("Couldn't read the asm_instr in the file\n");
            return;
        }
        fclose(fd);
    }
    printf("The asm string to emulate: %s\n", asm_instr);

    // Keystone Ops
    k_err = ks_open(KS_ARCH_X86, KS_MODE_64, &ks);
    if (k_err != KS_ERR_OK) {
        printf("ERROR: failed on ks_open(), quit\n");
        return;
    }
    if (!k_err) {
        ks_option(ks, KS_OPT_SYNTAX, KS_OPT_SYNTAX_ATT);
    }

    k_err = ks_asm(ks, asm_instr, 0, &encode, &size, &count);
    if( k_err != KS_ERR_OK) {
        printf("ERROR: ks_asm() failed & count = %lu, error = %u\n", count, ks_errno(ks));

        // cleanup KS
        ks_close(ks);
        return;
    } else {
        size_t i;
        printf("assembled code in hex is \n");
        for(i = 0; i < size; i++) {
            printf("%02x ", encode[i]);
        }
        printf("\n");
        printf("Compiled: %lu bytes, statements: %lu\n", size, count);
    }

    // below code is imp
    int64_t rsp = ADDRESS + 0x200000;
    state->rflags = (0x8c5 & state->rflags);        // Necessary code.

    printf("Emulate x86_64 code\n");

    // Initialize emulator in X86-64bit mode
    err = uc_open(UC_ARCH_X86, UC_MODE_64, &uc);
    if (err) {
        printf("Failed on uc_open() with error returned: %u\n", err);
        return;
    }

    // map 2MB memory for this emulation
    uc_mem_map(uc, ADDRESS, 2 * 1024 * 1024, UC_PROT_ALL);

    // write machine code to be emulated to memory
    if (uc_mem_write(uc, ADDRESS, encode, size)) {
        printf("Failed to write emulation code to memory, quit!\n");

        // cleanup UC
        uc_close(uc);

        // cleanup KS
        ks_free(encode);
        ks_close(ks);

        return;
    }

    // initialize machine registers
    uc_reg_write(uc, UC_X86_REG_RSP, &rsp);             // special case

    uc_reg_write(uc, UC_X86_REG_RAX, &state->rax);
    uc_reg_write(uc, UC_X86_REG_RBX, &state->rbx);
    uc_reg_write(uc, UC_X86_REG_RCX, &state->rcx);
    uc_reg_write(uc, UC_X86_REG_RDX, &state->rdx);
    uc_reg_write(uc, UC_X86_REG_RSI, &state->rsi);
    uc_reg_write(uc, UC_X86_REG_RDI, &state->rdi);
    uc_reg_write(uc, UC_X86_REG_R8, &state->r8);
    uc_reg_write(uc, UC_X86_REG_R9, &state->r9);
    uc_reg_write(uc, UC_X86_REG_R10, &state->r10);
    uc_reg_write(uc, UC_X86_REG_R11, &state->r11);
    uc_reg_write(uc, UC_X86_REG_R12, &state->r12);
    uc_reg_write(uc, UC_X86_REG_R13, &state->r13);
    uc_reg_write(uc, UC_X86_REG_R14, &state->r14);
    uc_reg_write(uc, UC_X86_REG_R15, &state->r15);
    uc_reg_write(uc, UC_X86_REG_RFLAGS, &state->rflags);
    uc_reg_write(uc, UC_X86_REG_XMM0, &state->xmm0);
    uc_reg_write(uc, UC_X86_REG_XMM1, &state->xmm1);
    uc_reg_write(uc, UC_X86_REG_XMM2, &state->xmm2);
    uc_reg_write(uc, UC_X86_REG_XMM3, &state->xmm3);
    uc_reg_write(uc, UC_X86_REG_XMM4, &state->xmm4);
    uc_reg_write(uc, UC_X86_REG_XMM5, &state->xmm5);
    uc_reg_write(uc, UC_X86_REG_XMM6, &state->xmm6);
    uc_reg_write(uc, UC_X86_REG_XMM7, &state->xmm7);
    uc_reg_write(uc, UC_X86_REG_XMM8, &state->xmm8);
    uc_reg_write(uc, UC_X86_REG_XMM9, &state->xmm9);
    uc_reg_write(uc, UC_X86_REG_XMM10, &state->xmm10);
    uc_reg_write(uc, UC_X86_REG_XMM11, &state->xmm11);
    uc_reg_write(uc, UC_X86_REG_XMM12, &state->xmm12);
    uc_reg_write(uc, UC_X86_REG_XMM13, &state->xmm13);
    uc_reg_write(uc, UC_X86_REG_XMM14, &state->xmm14);
    uc_reg_write(uc, UC_X86_REG_XMM15, &state->xmm15);

    // emulate machine code in infinite time (last param = 0), or when
    // finishing all the code.
    err = uc_emu_start(uc, ADDRESS, ADDRESS + size, 0, 0);
    if (err) {
        printf("Failed on uc_emu_start() with error returned %u: %s\n", err,
               uc_strerror(err));

        // cleanup UC
        uc_close(uc);

        // cleanup KS
        ks_free(encode);
        ks_close(ks);

        return;
    }

    // now print out some registers
    printf("Emulation done. Below is the CPU context\n");

    uc_reg_read(uc, UC_X86_REG_RAX, &state->rax);
    uc_reg_read(uc, UC_X86_REG_RBX, &state->rbx);
    uc_reg_read(uc, UC_X86_REG_RCX, &state->rcx);
    uc_reg_read(uc, UC_X86_REG_RDX, &state->rdx);
    uc_reg_read(uc, UC_X86_REG_RSI, &state->rsi);
    uc_reg_read(uc, UC_X86_REG_RDI, &state->rdi);
    uc_reg_read(uc, UC_X86_REG_R8, &state->r8);
    uc_reg_read(uc, UC_X86_REG_R9, &state->r9);
    uc_reg_read(uc, UC_X86_REG_R10, &state->r10);
    uc_reg_read(uc, UC_X86_REG_R11, &state->r11);
    uc_reg_read(uc, UC_X86_REG_R12, &state->r12);
    uc_reg_read(uc, UC_X86_REG_R13, &state->r13);
    uc_reg_read(uc, UC_X86_REG_R14, &state->r14);
    uc_reg_read(uc, UC_X86_REG_R15, &state->r15);
    uc_reg_read(uc, UC_X86_REG_RFLAGS, &state->rflags);
    uc_reg_read(uc, UC_X86_REG_XMM0, &state->xmm0);
    uc_reg_read(uc, UC_X86_REG_XMM1, &state->xmm1);
    uc_reg_read(uc, UC_X86_REG_XMM2, &state->xmm2);
    uc_reg_read(uc, UC_X86_REG_XMM3, &state->xmm3);
    uc_reg_read(uc, UC_X86_REG_XMM4, &state->xmm4);
    uc_reg_read(uc, UC_X86_REG_XMM5, &state->xmm5);
    uc_reg_read(uc, UC_X86_REG_XMM6, &state->xmm6);
    uc_reg_read(uc, UC_X86_REG_XMM7, &state->xmm7);
    uc_reg_read(uc, UC_X86_REG_XMM8, &state->xmm8);
    uc_reg_read(uc, UC_X86_REG_XMM9, &state->xmm9);
    uc_reg_read(uc, UC_X86_REG_XMM10, &state->xmm10);
    uc_reg_read(uc, UC_X86_REG_XMM11, &state->xmm11);
    uc_reg_read(uc, UC_X86_REG_XMM12, &state->xmm12);
    uc_reg_read(uc, UC_X86_REG_XMM13, &state->xmm13);
    uc_reg_read(uc, UC_X86_REG_XMM14, &state->xmm14);
    uc_reg_read(uc, UC_X86_REG_XMM15, &state->xmm15);

    printf("UC_RAX = 0x%" PRIx64 "\n", state->rax);
    printf("UC_RBX = 0x%" PRIx64 "\n", state->rbx);
    printf("UC_RCX = 0x%" PRIx64 "\n", state->rcx);
    printf("UC_RDX = 0x%" PRIx64 "\n", state->rdx);
    printf("UC_RSI = 0x%" PRIx64 "\n", state->rsi);
    printf("UC_RDI = 0x%" PRIx64 "\n", state->rdi);
    printf("UC_R8 = 0x%" PRIx64 "\n", state->r8);
    printf("UC_R9 = 0x%" PRIx64 "\n", state->r9);
    printf("UC_R10 = 0x%" PRIx64 "\n", state->r10);
    printf("UC_R11 = 0x%" PRIx64 "\n", state->r11);
    printf("UC_R12 = 0x%" PRIx64 "\n", state->r12);
    printf("UC_R13 = 0x%" PRIx64 "\n", state->r13);
    printf("UC_R14 = 0x%" PRIx64 "\n", state->r14);
    printf("UC_R15 = 0x%" PRIx64 "\n", state->r15);
    printf("UC_RFLAGS = 0x%" PRIx64 "\n", state->rflags);
    printf("UC_XMM0 = 0x%" PRIx64 "\n", state->xmm0);
    printf("UC_XMM1 = 0x%" PRIx64 "\n", state->xmm1);
    printf("UC_XMM2 = 0x%" PRIx64 "\n", state->xmm2);
    printf("UC_XMM3 = 0x%" PRIx64 "\n", state->xmm3);
    printf("UC_XMM4 = 0x%" PRIx64 "\n", state->xmm4);
    printf("UC_XMM5 = 0x%" PRIx64 "\n", state->xmm5);
    printf("UC_XMM6 = 0x%" PRIx64 "\n", state->xmm6);
    printf("UC_XMM7 = 0x%" PRIx64 "\n", state->xmm7);
    printf("UC_XMM8 = 0x%" PRIx64 "\n", state->xmm8);
    printf("UC_XMM9 = 0x%" PRIx64 "\n", state->xmm9);
    printf("UC_XMM10 = 0x%" PRIx64 "\n", state->xmm10);
    printf("UC_XMM11 = 0x%" PRIx64 "\n", state->xmm11);
    printf("UC_XMM12 = 0x%" PRIx64 "\n", state->xmm12);
    printf("UC_XMM13 = 0x%" PRIx64 "\n", state->xmm13);
    printf("UC_XMM14 = 0x%" PRIx64 "\n", state->xmm14);
    printf("UC_XMM15 = 0x%" PRIx64 "\n", state->xmm15);

    // cleanup UC
    uc_close(uc);

    // cleanup KS
    ks_free(encode);
    ks_close(ks);
}
*/
