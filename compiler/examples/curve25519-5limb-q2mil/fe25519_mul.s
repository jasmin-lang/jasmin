	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_fe25519_mul
	.globl	crypto_scalarmult_curve25519_amd64_51_fe25519_mul
_crypto_scalarmult_curve25519_amd64_51_fe25519_mul:
crypto_scalarmult_curve25519_amd64_51_fe25519_mul:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$16, %rsp
	movq	%rdx, %rcx
	movq	24(%rsi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, (%rsp)
	mulq	16(%rcx)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	32(%rsi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	8(%rcx)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	(%rsi), %rax
	mulq	8(%rcx)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	(%rsi), %rax
	mulq	16(%rcx)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	(%rsi), %rax
	mulq	24(%rcx)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	(%rsi), %rax
	mulq	32(%rcx)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	8(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	8(%rsi), %rax
	mulq	16(%rcx)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	8(%rsi), %rax
	mulq	24(%rcx)
	addq	%rax, %r14
	adcq	%rdx, %r15
	movq	8(%rsi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rcx)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	16(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	16(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	16(%rsi), %rax
	mulq	16(%rcx)
	addq	%rax, %r14
	adcq	%rdx, %r15
	movq	16(%rsi), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rcx)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	16(%rsi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rcx)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	24(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	24(%rsi), %rax
	mulq	8(%rcx)
	addq	%rax, %r14
	adcq	%rdx, %r15
	movq	(%rsp), %rax
	mulq	24(%rcx)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	(%rsp), %rax
	mulq	32(%rcx)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	32(%rsi), %rax
	mulq	(%rcx)
	addq	%rax, %r14
	adcq	%rdx, %r15
	movq	8(%rsp), %rax
	mulq	16(%rcx)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	24(%rcx)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	8(%rsp), %rax
	mulq	32(%rcx)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	$2251799813685247, %rax
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rcx
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %rdx
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %rsi
	shldq	$13, %r14, %r15
	andq	%rax, %r14
	leaq	(%r14,%r13), %r9
	imulq	$19, %r15, %r15
	leaq	(%r8,%r15), %r10
	movq	%r10, %r8
	shrq	$51, %r8
	leaq	(%r8,%rcx), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r8
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %rsi
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, (%rdi)
	movq	%r8, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	movq	%r9, 32(%rdi)
	addq	$16, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
