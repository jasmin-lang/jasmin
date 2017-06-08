	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_work_cswap
	.globl	crypto_scalarmult_curve25519_amd64_64_work_cswap
_crypto_scalarmult_curve25519_amd64_64_work_cswap:
crypto_scalarmult_curve25519_amd64_64_work_cswap:
	pushq	%rbp
	cmpq	$1, %rsi
	movq	(%rdi), %rcx
	movq	64(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, (%rdi)
	movq	%rdx, 64(%rdi)
	movq	8(%rdi), %rcx
	movq	72(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 8(%rdi)
	movq	%rdx, 72(%rdi)
	movq	16(%rdi), %rcx
	movq	80(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 16(%rdi)
	movq	%rdx, 80(%rdi)
	movq	24(%rdi), %rcx
	movq	88(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 24(%rdi)
	movq	%rdx, 88(%rdi)
	movq	32(%rdi), %rcx
	movq	96(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 32(%rdi)
	movq	%rdx, 96(%rdi)
	movq	40(%rdi), %rcx
	movq	104(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 40(%rdi)
	movq	%rdx, 104(%rdi)
	movq	48(%rdi), %rcx
	movq	112(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 48(%rdi)
	movq	%rdx, 112(%rdi)
	movq	56(%rdi), %rcx
	movq	120(%rdi), %rdx
	movq	%rcx, %rax
	cmoveq	%rdx, %rcx
	cmoveq	%rax, %rdx
	movq	%rcx, 56(%rdi)
	movq	%rdx, 120(%rdi)
	popq	%rbp
	ret 
