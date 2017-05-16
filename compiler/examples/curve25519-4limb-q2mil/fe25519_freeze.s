	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_fe25519_freeze
	.globl	crypto_scalarmult_curve25519_amd64_64_fe25519_freeze
_crypto_scalarmult_curve25519_amd64_64_fe25519_freeze:
crypto_scalarmult_curve25519_amd64_64_fe25519_freeze:
	pushq	%rbp
	pushq	%rsi
	movq	(%rdi), %rax
	movq	8(%rdi), %rcx
	movq	16(%rdi), %rdx
	movq	24(%rdi), %rsi
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%rdx, %r11
	movq	%rsi, %rbp
	movq	$1, %r8
	shlq	$63, %r8
	addq	$19, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	%r8, %rbp
	cmovbq	%r9, %rax
	cmovbq	%r10, %rcx
	cmovbq	%r11, %rdx
	cmovbq	%rbp, %rsi
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%rdx, %r11
	movq	%rsi, %rbp
	addq	$19, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	%r8, %rbp
	cmovbq	%r9, %rax
	cmovbq	%r10, %rcx
	cmovbq	%r11, %rdx
	cmovbq	%rbp, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
