	.text
	.p2align	5
	.globl	_iterated_square_export
	.globl	iterated_square_export
_iterated_square_export:
iterated_square_export:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$16, %rsp
	movq	(%rdi), %rcx
	movq	8(%rdi), %r13
	movq	16(%rdi), %r14
	movq	24(%rdi), %r15
	movq	%rsi, (%rsp)
	jmp 	L1
L2:
L1:
	movq	%r13, %rax
	mulq	%rcx
	movq	%rax, %rbx
	movq	%rdx, %rsi
	movq	%r14, %rax
	mulq	%r13
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	%r15, %rax
	mulq	%r14
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	$0, %rbp
	movq	%r14, %rax
	mulq	%rcx
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	%r15, %rax
	mulq	%r13
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	%r15, %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r12
	movq	%r13, %rax
	mulq	%r13
	movq	%rax, %r13
	movq	%rdx, 8(%rsp)
	movq	%r14, %rax
	mulq	%r14
	movq	8(%rsp), %r14
	addq	%r12, %rbx
	adcq	%r13, %rsi
	adcq	%r14, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	%r15, %rax
	mulq	%r15
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r13
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r14
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r15
	movq	%rbp, %rax
	adcq	%rdx, %r15
	mulq	__38(%rip)
	addq	%rax, %r15
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r9
	adcq	%rbx, %r13
	adcq	%rsi, %r14
	adcq	%r8, %r15
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	$0, %r13
	adcq	$0, %r14
	adcq	$0, %r15
	adcq	$0, %rcx
	imulq	$38, %rcx, %rcx
	leaq	(%r9,%rcx), %rcx
	subq	$1, (%rsp)
	jnb 	L2
	movq	%rcx, (%rdi)
	movq	%r13, 8(%rdi)
	movq	%r14, 16(%rdi)
	movq	%r15, 24(%rdi)
	addq	$16, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
	.data
	.globl	___38
	.globl	__38
	.align	8
___38:
__38:
	.quad	38
