	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_fe25519_square
	.globl	crypto_scalarmult_curve25519_amd64_64_fe25519_square
_crypto_scalarmult_curve25519_amd64_64_fe25519_square:
crypto_scalarmult_curve25519_amd64_64_fe25519_square:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	$0, %rbp
	movq	8(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	16(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	24(%rsi), %rax
	mulq	16(%rsi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	16(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	24(%rsi), %rax
	mulq	8(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	24(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	8(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	16(%rsi), %rax
	mulq	16(%rsi)
	addq	%r12, %rbx
	adcq	%r13, %rcx
	adcq	%r14, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	24(%rsi), %rax
	mulq	24(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	%r9, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rsi
	movq	%r10, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r11, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbp, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r15
	adcq	%r9, %rbx
	adcq	%r10, %rcx
	adcq	%r11, %r8
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rdx, %rbx
	adcq	%rdx, %rcx
	adcq	%rdx, %r8
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r15
	movq	%rbx, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movq	%r8, 24(%rdi)
	movq	%r15, (%rdi)
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
