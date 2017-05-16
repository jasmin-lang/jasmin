.text
.p2align 5
.globl _crypto_scalarmult_curve25519_amd64_64_fe25519_square
.globl crypto_scalarmult_curve25519_amd64_64_fe25519_square
_crypto_scalarmult_curve25519_amd64_64_fe25519_square:
crypto_scalarmult_curve25519_amd64_64_fe25519_square:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	$0, %rcx
	movq	8(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	16(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	24(%rsi), %rax
	mulq	16(%rsi)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	16(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	24(%rsi), %rax
	mulq	8(%rsi)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	movq	24(%rsi), %rax
	mulq	(%rsi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	(%rsi), %rax
	mulq	(%rsi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	8(%rsi), %rax
	mulq	8(%rsi)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	16(%rsi), %rax
	mulq	16(%rsi)
	addq	%r13, %r8
	adcq	%r14, %r9
	adcq	%r15, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	24(%rsi), %rax
	mulq	24(%rsi)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r11
	movq	%rbp, %rax
	movq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%rbx, %rax
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbx
	movq	%rcx, %rax
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rcx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r11, %r12
	adcq	%rbp, %r8
	adcq	%rbx, %r9
	adcq	%rcx, %r10
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r12
	movq	%r8, 8(%rdi)
	movq	%r9, 16(%rdi)
	movq	%r10, 24(%rdi)
	movq	%r12, (%rdi)
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret
