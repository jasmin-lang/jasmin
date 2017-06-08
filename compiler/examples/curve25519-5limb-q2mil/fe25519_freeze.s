	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_fe25519_freeze
	.globl	crypto_scalarmult_curve25519_amd64_51_fe25519_freeze
_crypto_scalarmult_curve25519_amd64_51_fe25519_freeze:
crypto_scalarmult_curve25519_amd64_51_fe25519_freeze:
	pushq	%rbp
	pushq	%rsi
	movq	(%rdi), %rdx
	movq	8(%rdi), %rsi
	movq	16(%rdi), %r8
	movq	24(%rdi), %r9
	movq	32(%rdi), %r10
	movq	$2251799813685247, %rbp
	movq	%rbp, %rax
	subq	$18, %rax
	movq	$3, %r11
	jmp 	L1
L2:
	movq	%rdx, %rcx
	shrq	$51, %rcx
	andq	%rbp, %rdx
	leaq	(%rsi,%rcx), %rsi
	movq	%rsi, %rcx
	shrq	$51, %rcx
	andq	%rbp, %rsi
	leaq	(%r8,%rcx), %r8
	movq	%r8, %rcx
	shrq	$51, %rcx
	andq	%rbp, %r8
	leaq	(%r9,%rcx), %r9
	movq	%r9, %rcx
	shrq	$51, %rcx
	andq	%rbp, %r9
	leaq	(%r10,%rcx), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	andq	%rbp, %r10
	imulq	$19, %rcx, %rcx
	leaq	(%rdx,%rcx), %rdx
	decq	%r11
L1:
	cmpq	$0, %r11
	jnbe	L2
	movq	$1, %rcx
	cmpq	%rax, %rdx
	cmovlq	%r11, %rcx
	cmpq	%rbp, %rsi
	cmovneq	%r11, %rcx
	cmpq	%rbp, %r8
	cmovneq	%r11, %rcx
	cmpq	%rbp, %r9
	cmovneq	%r11, %rcx
	cmpq	%rbp, %r10
	cmovneq	%r11, %rcx
	negq	%rcx
	andq	%rcx, %rbp
	andq	%rcx, %rax
	subq	%rax, %rdx
	subq	%rbp, %rsi
	subq	%rbp, %r8
	subq	%rbp, %r9
	subq	%rbp, %r10
	movq	%rdx, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%r9, 24(%rdi)
	movq	%r10, 32(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
