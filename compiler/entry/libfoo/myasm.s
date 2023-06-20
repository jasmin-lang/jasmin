    .att_syntax
    .text
    .p2align    5
    .globl  _set_execute_get
    .globl  set_execute_get
_set_execute_get:
set_execute_get:
    movq     %rsp, %rax             #mov sp value to eax to save later
    leaq    -72(%rsp), %rsp         # make space on the stack for callee saved regs
    andq    $-8, %rsp               # align the address
    movq    %rax, 64(%rsp)          # save rsp
    movq    %rbx, (%rsp)            # save rbx
    movq    %rbp, 8(%rsp)           # save rbp
    movq    %r12, 16(%rsp)          # save r12
    movq    %r13, 24(%rsp)          # save r13
    movq    %r14, 32(%rsp)          # save r14
    movq    %r15, 40(%rsp)          # save r15
    movq    %rdi, 48(%rsp)          # save rdi argument

    # move to registers except rsp
    movq    (%rdi), %rax
    movq    8(%rdi), %rbx
    movq    16(%rdi), %rcx
    movq    24(%rdi), %rdx
    movq    64(%rdi), %r8
    movq    72(%rdi), %r9
    movq    80(%rdi), %r10
    movq    88(%rdi), %r11
    movq    96(%rdi), %r12
    movq    104(%rdi), %r13
    movq    112(%rdi), %r14
    movq    120(%rdi), %r15
    movq    32(%rdi), %rsi
    movq    56(%rdi), %rbp
    movq    40(%rdi), %rdi

    # execute the instruction
    # TODO: to be filled here
    incq    %rax

    # save the post execution rdi value
    movq    %rdi, 56(%rsp)

    # restore the rdi value saved on stack
    movq    48(%rsp), %rdi

    # post execution register values
    movq    %rax, (%rdi)
    movq    %rbx, 8(%rdi)
    movq    %rcx, 16(%rdi)
    movq    %rdx, 24(%rdi)
    movq    %r8, 64(%rdi)
    movq    %r9, 72(%rdi)
    movq    %r10, 80(%rdi)
    movq    %r11, 88(%rdi)
    movq    %r12, 96(%rdi)
    movq    %r13, 104(%rdi)
    movq    %r14, 112(%rdi)
    movq    %r15, 120(%rdi)
    movq    %rsi, 32(%rdi)
    movq    %rbp, 56(%rdi)
    movq    %rsp, 48(%rdi)

    # get post-exec rdi
    movq    56(%rsp), %rax          # reusing rax
    movq    %rax, 40(%rdi)

    # get flag value
    pushfq
    popq    %rax                    # get rflags
    movq    %rax, 128(%rdi)

    movq    (%rsp), %rbx            # restore rbx
    movq    8(%rsp), %rbp           # restore rbp
    movq    16(%rsp), %r12          # restore r12
    movq    24(%rsp), %r13          # restore r13
    movq    32(%rsp), %r14          # restore r14
    movq    40(%rsp), %r15          # restore r15
    movq    64(%rsp), %rsp          # restore rsp
    ret
