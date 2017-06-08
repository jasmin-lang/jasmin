	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_work_cswap
	.globl	crypto_scalarmult_curve25519_amd64_51_work_cswap
_crypto_scalarmult_curve25519_amd64_51_work_cswap:
crypto_scalarmult_curve25519_amd64_51_work_cswap:
	pushq	%rbp
	pushq	%rsi
	cmpq	$1, %rsi
	movq	(%rdi), %rcx
	movq	80(%rdi), %rdx
	movq	8(%rdi), %rsi
	movq	88(%rdi), %r8
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rsi, %rax
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	movq	%rcx, (%rdi)
	movq	%rdx, 80(%rdi)
	movq	%rsi, 8(%rdi)
	movq	%r8, 88(%rdi)
	movq	16(%rdi), %rcx
	movq	96(%rdi), %rdx
	movq	24(%rdi), %rsi
	movq	104(%rdi), %r8
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rsi, %rax
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	movq	%rcx, 16(%rdi)
	movq	%rdx, 96(%rdi)
	movq	%rsi, 24(%rdi)
	movq	%r8, 104(%rdi)
	movq	32(%rdi), %rcx
	movq	112(%rdi), %rdx
	movq	40(%rdi), %rsi
	movq	120(%rdi), %r8
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rsi, %rax
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	movq	%rcx, 32(%rdi)
	movq	%rdx, 112(%rdi)
	movq	%rsi, 40(%rdi)
	movq	%r8, 120(%rdi)
	movq	48(%rdi), %rcx
	movq	128(%rdi), %rdx
	movq	56(%rdi), %rsi
	movq	136(%rdi), %r8
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rsi, %rax
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	movq	%rcx, 48(%rdi)
	movq	%rdx, 128(%rdi)
	movq	%rsi, 56(%rdi)
	movq	%r8, 136(%rdi)
	movq	64(%rdi), %rcx
	movq	144(%rdi), %rdx
	movq	72(%rdi), %rsi
	movq	152(%rdi), %r8
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rsi, %rax
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	movq	%rcx, 64(%rdi)
	movq	%rdx, 144(%rdi)
	movq	%rsi, 72(%rdi)
	movq	%r8, 152(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
