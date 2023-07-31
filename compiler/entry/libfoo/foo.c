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
    printf("rflags = %lx\n", state->rflags);
}

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

    // cleanup UC
    uc_close(uc);

    // cleanup KS
    ks_free(encode);
    ks_close(ks);
}
