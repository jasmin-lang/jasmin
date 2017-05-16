	.globl	_F1
_F1:
	pushq	%rbp
	movq	%rsp, %rbp
	pushq	%rsi
	movq	(%rdi), %rax
	movq	8(%rdi), %rcx
	movq	16(%rdi), %rdx
	movq	24(%rdi), %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	movq	$1, %rbp
	shlq	$63, %rbp
	addq	$19, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	%rbp, %r11
	cmovbq	%r8, %rax
	cmovbq	%r9, %rcx
	cmovbq	%r10, %rdx
	cmovbq	%r11, %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	addq	$19, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	%rbp, %r11
	cmovbq	%r8, %rax
	cmovbq	%r9, %rcx
	cmovbq	%r10, %rdx
	cmovbq	%r11, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	leave
	ret 
