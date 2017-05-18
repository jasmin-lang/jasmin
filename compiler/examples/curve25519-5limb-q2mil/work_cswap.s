	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_work_cswap
	.globl	crypto_scalarmult_curve25519_amd64_51_work_cswap
_crypto_scalarmult_curve25519_amd64_51_work_cswap:
crypto_scalarmult_curve25519_amd64_51_work_cswap:
	pushq	%rbp
	pushq	%rsi
	cmpq	$1, %rsi
	movq	(%rdi), %rax
	movq	80(%rdi), %rcx
	movq	8(%rdi), %rdx
	movq	88(%rdi), %rsi
	movq	%rax, %r8
	cmoveq	%rcx, %rax
	cmoveq	%r8, %rcx
	movq	%rdx, %r8
	cmoveq	%rsi, %rdx
	cmoveq	%r8, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 80(%rdi)
	movq	%rdx, 8(%rdi)
	movq	%rsi, 88(%rdi)
	movq	16(%rdi), %rax
	movq	96(%rdi), %rcx
	movq	24(%rdi), %rdx
	movq	104(%rdi), %rsi
	movq	%rax, %r8
	cmoveq	%rcx, %rax
	cmoveq	%r8, %rcx
	movq	%rdx, %r8
	cmoveq	%rsi, %rdx
	cmoveq	%r8, %rsi
	movq	%rax, 16(%rdi)
	movq	%rcx, 96(%rdi)
	movq	%rdx, 24(%rdi)
	movq	%rsi, 104(%rdi)
	movq	32(%rdi), %rax
	movq	112(%rdi), %rcx
	movq	40(%rdi), %rdx
	movq	120(%rdi), %rsi
	movq	%rax, %r8
	cmoveq	%rcx, %rax
	cmoveq	%r8, %rcx
	movq	%rdx, %r8
	cmoveq	%rsi, %rdx
	cmoveq	%r8, %rsi
	movq	%rax, 32(%rdi)
	movq	%rcx, 112(%rdi)
	movq	%rdx, 40(%rdi)
	movq	%rsi, 120(%rdi)
	movq	48(%rdi), %rax
	movq	128(%rdi), %rcx
	movq	56(%rdi), %rdx
	movq	136(%rdi), %rsi
	movq	%rax, %r8
	cmoveq	%rcx, %rax
	cmoveq	%r8, %rcx
	movq	%rdx, %r8
	cmoveq	%rsi, %rdx
	cmoveq	%r8, %rsi
	movq	%rax, 48(%rdi)
	movq	%rcx, 128(%rdi)
	movq	%rdx, 56(%rdi)
	movq	%rsi, 136(%rdi)
	movq	64(%rdi), %rax
	movq	144(%rdi), %rcx
	movq	72(%rdi), %rdx
	movq	152(%rdi), %rsi
	movq	%rax, %r8
	cmoveq	%rcx, %rax
	cmoveq	%r8, %rcx
	movq	%rdx, %r8
	cmoveq	%rsi, %rdx
	cmoveq	%r8, %rsi
	movq	%rax, 64(%rdi)
	movq	%rcx, 144(%rdi)
	movq	%rdx, 72(%rdi)
	movq	%rsi, 152(%rdi)
	popq	%rsi
	popq	%rbp
	ret 
