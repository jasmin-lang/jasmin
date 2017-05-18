	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_fe25519_square
	.globl	crypto_scalarmult_curve25519_amd64_51_fe25519_square
_crypto_scalarmult_curve25519_amd64_51_fe25519_square:
crypto_scalarmult_curve25519_amd64_51_fe25519_square:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	movq	(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	(%rsi), %rax
	shlq	$1, %rax
	mulq	8(%rsi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	(%rsi), %rax
	shlq	$1, %rax
	mulq	16(%rsi)
	movq	%rax, %rcx
	movq	%rdx, %r8
	movq	(%rsi), %rax
	shlq	$1, %rax
	mulq	24(%rsi)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	(%rsi), %rax
	shlq	$1, %rax
	mulq	32(%rsi)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	8(%rsi), %rax
	mulq	8(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	8(%rsi), %rax
	shlq	$1, %rax
	mulq	16(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	8(%rsi), %rax
	shlq	$1, %rax
	mulq	24(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	8(%rsi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsi)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	16(%rsi), %rax
	mulq	16(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	16(%rsi), %rax
	imulq	$38, %rax, %rax
	mulq	24(%rsi)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	16(%rsi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsi)
	addq	%rax, %r13
	adcq	%rdx, %r14
	movq	24(%rsi), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rsi)
	addq	%rax, %r13
	adcq	%rdx, %r14
	movq	24(%rsi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsi)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	32(%rsi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	$2251799813685247, %rax
	shldq	$13, %rbx, %r12
	andq	%rax, %rbx
	shldq	$13, %r13, %r14
	andq	%rax, %r13
	addq	%r12, %r13
	shldq	$13, %rcx, %r8
	andq	%rax, %rcx
	addq	%r14, %rcx
	shldq	$13, %r9, %r10
	andq	%rax, %r9
	addq	%r8, %r9
	shldq	$13, %r11, %rbp
	andq	%rax, %r11
	addq	%r10, %r11
	imulq	$19, %rbp, %rdx
	addq	%rdx, %rbx
	movq	%rbx, %rdx
	shrq	$51, %rdx
	addq	%r13, %rdx
	andq	%rax, %rbx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r9, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r11, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rbx
	andq	%rax, %r9
	movq	%rbx, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movq	%r8, 24(%rdi)
	movq	%r9, 32(%rdi)
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
