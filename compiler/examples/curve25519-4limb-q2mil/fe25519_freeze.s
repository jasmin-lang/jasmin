	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_fe25519_freeze
	.globl	crypto_scalarmult_curve25519_amd64_64_fe25519_freeze
_crypto_scalarmult_curve25519_amd64_64_fe25519_freeze:
crypto_scalarmult_curve25519_amd64_64_fe25519_freeze:
	pushq	%rbp
	pushq	%rsi
	movq	(%rdi), %r9
	movq	8(%rdi), %r10
	movq	16(%rdi), %r11
	movq	24(%rdi), %rbp
	movq	%r9, %rcx
	movq	%r10, %rdx
	movq	%r11, %rsi
	movq	%rbp, %r8
	movq	$1, %rax
	shlq	$63, %rax
	addq	$19, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	adcq	%rax, %r8
	cmovbq	%rcx, %r9
	cmovbq	%rdx, %r10
	cmovbq	%rsi, %r11
	cmovbq	%r8, %rbp
	movq	%r9, %rcx
	movq	%r10, %rdx
	movq	%r11, %rsi
	movq	%rbp, %r8
	addq	$19, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	adcq	%rax, %r8
	cmovbq	%rcx, %r9
	cmovbq	%rdx, %r10
	cmovbq	%rsi, %r11
	cmovbq	%r8, %rbp
	movq	%r9, (%rdi)
	movq	%r10, 8(%rdi)
	movq	%r11, 16(%rdi)
	movq	%rbp, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
