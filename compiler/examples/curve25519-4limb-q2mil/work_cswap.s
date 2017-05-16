	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_work_cswap
	.globl	crypto_scalarmult_curve25519_amd64_64_work_cswap
_crypto_scalarmult_curve25519_amd64_64_work_cswap:
crypto_scalarmult_curve25519_amd64_64_work_cswap:
	pushq	%rbp
	cmpq	$1, %rsi
	movq	(%rdi), %rax
	movq	64(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, (%rdi)
	movq	%rcx, 64(%rdi)
	movq	8(%rdi), %rax
	movq	72(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 8(%rdi)
	movq	%rcx, 72(%rdi)
	movq	16(%rdi), %rax
	movq	80(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 16(%rdi)
	movq	%rcx, 80(%rdi)
	movq	24(%rdi), %rax
	movq	88(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 24(%rdi)
	movq	%rcx, 88(%rdi)
	movq	32(%rdi), %rax
	movq	96(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 32(%rdi)
	movq	%rcx, 96(%rdi)
	movq	40(%rdi), %rax
	movq	104(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 40(%rdi)
	movq	%rcx, 104(%rdi)
	movq	48(%rdi), %rax
	movq	112(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 48(%rdi)
	movq	%rcx, 112(%rdi)
	movq	56(%rdi), %rax
	movq	120(%rdi), %rcx
	movq	%rax, %rdx
	cmoveq	%rcx, %rax
	cmoveq	%rdx, %rcx
	movq	%rax, 56(%rdi)
	movq	%rcx, 120(%rdi)
	popq	%rbp
	ret 
