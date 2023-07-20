    .att_syntax
    .text
    .p2align    4
    .globl  set_execute_get
    .type   set_execute_get,@function
set_execute_get:
    pushq   %rbp
    movq    %rsp, %rbp
    pushq   %rdi
    pushq   %rbx
    pushq   %rsi
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15
    pushfq

    # zero out the 5 flags supported by jasmin using AND
    pushf
    pop    %ax
    andw    $0x7b3a, %ax
    movq    128(%rdi), %rbx                 # move the generated flag value
    andw    $0x8c5, %bx                     # get only the required 5 bits
    orw     %bx, %ax                        # set the flags using OR
    push   %ax
    popf

    # start moving to registers
    movq    (%rdi), %rax
    movq    8(%rdi), %rcx
    movq    16(%rdi), %rdx
    movq    24(%rdi), %rbx
    # movq    32(%rdi), %rsp
    # movq    40(%rdi), %rbp
    movq    48(%rdi), %rsi
    # movq    56(%rdi), %rdi
    movq    64(%rdi), %r8
    movq    72(%rdi), %r9
    movq    80(%rdi), %r10
    movq    88(%rdi), %r11
    movq    96(%rdi), %r12
    movq    104(%rdi), %r13
    movq    112(%rdi), %r14
    movq    120(%rdi), %r15

    # move the rdi at last
    movq    56(%rdi), %rdi

    # Execute the instruction here
    cmovo   %rbx, %rax

    # post execution
    pushq   %rdi                    # save the post-exec rdi
    movq    -8(%rbp),   %rdi

    # restore
    movq    %rax, (%rdi)
    movq    %rcx, 8(%rdi)
    movq    %rdx, 16(%rdi)
    movq    %rbx, 24(%rdi)
    movq    %rsp, 32(%rdi)
    movq    %rbp, 40(%rdi)
    movq    %rsi, 48(%rdi)
    # movq  %rdi, 56(%rdi)
    movq    %r8, 64(%rdi)
    movq    %r9, 72(%rdi)
    movq    %r10, 80(%rdi)
    movq    %r11, 88(%rdi)
    movq    %r12, 96(%rdi)
    movq    %r13, 104(%rdi)
    movq    %r14, 112(%rdi)
    movq    %r15, 120(%rdi)

    # get flag value
    pushfq
    popq    %rax                    # get rflags
    movq    %rax, 128(%rdi)

    #recover the post-exec rdi
    popq    %rax
    movq    %rax, 56(%rdi)

    # move the rdi at last
    movq    56(%rdi), %rdi

    # restore callee saved registers
    popfq
    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %rsi
    popq    %rbx
    popq    %rdi
    popq    %rbp
    ret
