	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_fe25519_mul
	.globl	crypto_scalarmult_curve25519_amd64_64_fe25519_mul
_crypto_scalarmult_curve25519_amd64_64_fe25519_mul:
crypto_scalarmult_curve25519_amd64_64_fe25519_mul:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	%rdx, %rcx
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	(%rsi), %r8
	movq	(%rcx), %rax
	mulq	%r8
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	8(%rsi), %r8
	movq	(%rcx), %rax
	mulq	%r8
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	16(%rsi), %r8
	movq	(%rcx), %rax
	mulq	%r8
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rcx), %rax
	mulq	%r8
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rcx), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rcx), %rax
	mulq	%r8
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	24(%rsi), %rsi
	movq	(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r11
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	8(%rcx), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	16(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r8, %r12
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	24(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%r8, %r13
	adcq	%rdx, %r14
	movq	%rbp, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%r12, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r13, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r14, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%rsi, %r9
	adcq	%r8, %r10
	adcq	%rbp, %r11
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	leaq	(%r15,%rcx), %rax
	movq	%r9, 8(%rdi)
	movq	%r10, 16(%rdi)
	movq	%r11, 24(%rdi)
	movq	%rax, (%rdi)
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
