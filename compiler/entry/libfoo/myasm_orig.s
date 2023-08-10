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
    movq    640(%rdi), %rbx                 # move the generated flag value
    andw    $0x8c5, %bx                     # get only the required 5 bits
    orw     %bx, %ax                        # set the flags using OR
    push   %ax
    popf

    # mov to xmm registers
    vmovdqu   128(%rdi), %ymm0
    vmovdqu   160(%rdi), %ymm1
    vmovdqu   192(%rdi), %ymm2
    vmovdqu   224(%rdi), %ymm3
    vmovdqu   256(%rdi), %ymm4
    vmovdqu   288(%rdi), %ymm5
    vmovdqu   320(%rdi), %ymm6
    vmovdqu   352(%rdi), %ymm7
    vmovdqu   384(%rdi), %ymm8
    vmovdqu   416(%rdi), %ymm9
    vmovdqu   448(%rdi), %ymm10
    vmovdqu   480(%rdi), %ymm11
    vmovdqu   512(%rdi), %ymm12
    vmovdqu   544(%rdi), %ymm13
    vmovdqu   576(%rdi), %ymm14
    vmovdqu   608(%rdi), %ymm15

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
    replace_me

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

    # move from xmm registers
    vmovdqu   %ymm0, 128(%rdi)
    vmovdqu   %ymm1, 160(%rdi)
    vmovdqu   %ymm2, 192(%rdi)
    vmovdqu   %ymm3, 224(%rdi)
    vmovdqu   %ymm4, 256(%rdi)
    vmovdqu   %ymm5, 288(%rdi)
    vmovdqu   %ymm6, 320(%rdi)
    vmovdqu   %ymm7, 352(%rdi)
    vmovdqu   %ymm8, 384(%rdi)
    vmovdqu   %ymm9, 416(%rdi)
    vmovdqu   %ymm10, 448(%rdi)
    vmovdqu   %ymm11, 480(%rdi)
    vmovdqu   %ymm12, 512(%rdi)
    vmovdqu   %ymm13, 544(%rdi)
    vmovdqu   %ymm14, 576(%rdi)
    vmovdqu   %ymm15, 608(%rdi)

    # get flag value
    pushfq
    popq    %rax                    # get rflags
    movq    %rax, 640(%rdi)

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
