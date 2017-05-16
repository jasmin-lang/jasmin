	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_64_ladderstep
	.globl	crypto_scalarmult_curve25519_amd64_64_ladderstep
_crypto_scalarmult_curve25519_amd64_64_ladderstep:
crypto_scalarmult_curve25519_amd64_64_ladderstep:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	subq	$224, %rsp
	movq	32(%rdi), %rax
	movq	40(%rdi), %rcx
	movq	48(%rdi), %rdx
	movq	56(%rdi), %rsi
	movq	%rax, %r10
	movq	%rcx, %r11
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	addq	64(%rdi), %rax
	adcq	72(%rdi), %rcx
	adcq	80(%rdi), %rdx
	adcq	88(%rdi), %rsi
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	addq	%r9, %rax
	adcq	%r8, %rcx
	adcq	%r8, %rdx
	adcq	%r8, %rsi
	cmovbq	%r9, %r8
	addq	%r8, %rax
	subq	64(%rdi), %r10
	sbbq	72(%rdi), %r11
	sbbq	80(%rdi), %rbp
	sbbq	88(%rdi), %rbx
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	subq	%r9, %r10
	sbbq	%r8, %r11
	sbbq	%r8, %rbp
	sbbq	%r8, %rbx
	cmovbq	%r9, %r8
	subq	%r8, %r10
	movq	%rax, (%rsp)
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r10, 32(%rsp)
	movq	%r11, 40(%rsp)
	movq	%rbp, 48(%rsp)
	movq	%rbx, 56(%rsp)
	movq	$0, %r11
	movq	40(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	48(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	56(%rsp), %rax
	mulq	48(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	48(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	56(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	56(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	addq	%rbp, %rbp
	adcq	%rcx, %rcx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	32(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	40(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	48(%rsp), %rax
	mulq	48(%rsp)
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	56(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r14
	adcq	%r9, %rbp
	adcq	%r10, %rcx
	adcq	%r11, %rsi
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rdx, %rbp
	adcq	%rdx, %rcx
	adcq	%rdx, %rsi
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r14
	movq	%r14, 64(%rsp)
	movq	%rbp, 72(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%rsi, 88(%rsp)
	movq	$0, %r11
	movq	8(%rsp), %rax
	mulq	(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	16(%rsp), %rax
	mulq	8(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	24(%rsp), %rax
	mulq	16(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	16(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	24(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	24(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	addq	%rbp, %rbp
	adcq	%rcx, %rcx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	(%rsp), %rax
	mulq	(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	8(%rsp), %rax
	mulq	8(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	16(%rsp), %rax
	mulq	16(%rsp)
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	24(%rsp), %rax
	mulq	24(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r14
	adcq	%r9, %rbp
	adcq	%r10, %rcx
	adcq	%r11, %rsi
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rdx, %rbp
	adcq	%rdx, %rcx
	adcq	%rdx, %rsi
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r14
	movq	%r14, 96(%rsp)
	movq	%rbp, 104(%rsp)
	movq	%rcx, 112(%rsp)
	movq	%rsi, 120(%rsp)
	movq	%r14, %rax
	movq	%rbp, %rdx
	movq	%rcx, %rcx
	movq	%rsi, %rsi
	subq	64(%rsp), %rax
	sbbq	72(%rsp), %rdx
	sbbq	80(%rsp), %rcx
	sbbq	88(%rsp), %rsi
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	subq	%r9, %rax
	sbbq	%r8, %rdx
	sbbq	%r8, %rcx
	sbbq	%r8, %rsi
	cmovbq	%r9, %r8
	subq	%r8, %rax
	movq	%rax, 128(%rsp)
	movq	%rdx, 136(%rsp)
	movq	%rcx, 144(%rsp)
	movq	%rsi, 152(%rsp)
	movq	96(%rdi), %rax
	movq	104(%rdi), %rcx
	movq	112(%rdi), %rdx
	movq	120(%rdi), %rsi
	movq	%rax, %r10
	movq	%rcx, %r11
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	addq	128(%rdi), %rax
	adcq	136(%rdi), %rcx
	adcq	144(%rdi), %rdx
	adcq	152(%rdi), %rsi
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	addq	%r9, %rax
	adcq	%r8, %rcx
	adcq	%r8, %rdx
	adcq	%r8, %rsi
	cmovbq	%r9, %r8
	addq	%r8, %rax
	subq	128(%rdi), %r10
	sbbq	136(%rdi), %r11
	sbbq	144(%rdi), %rbp
	sbbq	152(%rdi), %rbx
	movq	$0, %r8
	movq	$38, %r9
	cmovnbq	%r8, %r9
	subq	%r9, %r10
	sbbq	%r8, %r11
	sbbq	%r8, %rbp
	sbbq	%r8, %rbx
	cmovbq	%r9, %r8
	subq	%r8, %r10
	movq	%rax, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rdx, 176(%rsp)
	movq	%rsi, 184(%rsp)
	movq	%r10, 192(%rsp)
	movq	%r11, 200(%rsp)
	movq	%rbp, 208(%rsp)
	movq	%rbx, 216(%rsp)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	160(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	168(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	176(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	184(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 32(%rsp)
	movq	%rsi, 40(%rsp)
	movq	%r8, 48(%rsp)
	movq	%r9, 56(%rsp)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	192(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	200(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	208(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	216(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, %rax
	movq	%rsi, %rcx
	movq	%r8, %rdx
	movq	%r9, %r10
	subq	32(%rsp), %rax
	sbbq	40(%rsp), %rcx
	sbbq	48(%rsp), %rdx
	sbbq	56(%rsp), %r10
	movq	$0, %r11
	movq	$38, %rbp
	cmovnbq	%r11, %rbp
	subq	%rbp, %rax
	sbbq	%r11, %rcx
	sbbq	%r11, %rdx
	sbbq	%r11, %r10
	cmovbq	%rbp, %r11
	subq	%r11, %rax
	addq	32(%rsp), %r13
	adcq	40(%rsp), %rsi
	adcq	48(%rsp), %r8
	adcq	56(%rsp), %r9
	movq	$0, %r11
	movq	$38, %rbp
	cmovnbq	%r11, %rbp
	addq	%rbp, %r13
	adcq	%r11, %rsi
	adcq	%r11, %r8
	adcq	%r11, %r9
	cmovbq	%rbp, %r11
	addq	%r11, %r13
	movq	%r13, 96(%rdi)
	movq	%rsi, 104(%rdi)
	movq	%r8, 112(%rdi)
	movq	%r9, 120(%rdi)
	movq	%rax, 128(%rdi)
	movq	%rcx, 136(%rdi)
	movq	%rdx, 144(%rdi)
	movq	%r10, 152(%rdi)
	movq	$0, %r11
	movq	104(%rdi), %rax
	mulq	96(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	112(%rdi), %rax
	mulq	104(%rdi)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	120(%rdi), %rax
	mulq	112(%rdi)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	112(%rdi), %rax
	mulq	96(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	120(%rdi), %rax
	mulq	104(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	120(%rdi), %rax
	mulq	96(%rdi)
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	addq	%rbp, %rbp
	adcq	%rcx, %rcx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	96(%rdi), %rax
	mulq	96(%rdi)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	104(%rdi), %rax
	mulq	104(%rdi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	112(%rdi), %rax
	mulq	112(%rdi)
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	120(%rdi), %rax
	mulq	120(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r14
	adcq	%r9, %rbp
	adcq	%r10, %rcx
	adcq	%r11, %rsi
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rdx, %rbp
	adcq	%rdx, %rcx
	adcq	%rdx, %rsi
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r14
	movq	%r14, 96(%rdi)
	movq	%rbp, 104(%rdi)
	movq	%rcx, 112(%rdi)
	movq	%rsi, 120(%rdi)
	movq	$0, %r11
	movq	136(%rdi), %rax
	mulq	128(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	144(%rdi), %rax
	mulq	136(%rdi)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	152(%rdi), %rax
	mulq	144(%rdi)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	144(%rdi), %rax
	mulq	128(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	152(%rdi), %rax
	mulq	136(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	152(%rdi), %rax
	mulq	128(%rdi)
	addq	%rax, %rsi
	adcq	%rdx, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	addq	%rbp, %rbp
	adcq	%rcx, %rcx
	adcq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	movq	128(%rdi), %rax
	mulq	128(%rdi)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	136(%rdi), %rax
	mulq	136(%rdi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	144(%rdi), %rax
	mulq	144(%rdi)
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	152(%rdi), %rax
	mulq	152(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r14
	adcq	%r9, %rbp
	adcq	%r10, %rcx
	adcq	%r11, %rsi
	movq	$0, %rdx
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	%rdx, %rbp
	adcq	%rdx, %rcx
	adcq	%rdx, %rsi
	adcq	%rdx, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r14
	movq	%r14, 128(%rdi)
	movq	%rbp, 136(%rdi)
	movq	%rcx, 144(%rdi)
	movq	%rsi, 152(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	128(%rdi), %rcx
	movq	(%rdi), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	8(%rdi), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	16(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	24(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	136(%rdi), %rcx
	movq	(%rdi), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	144(%rdi), %rcx
	movq	(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rdi), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	152(%rdi), %rcx
	movq	(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rdi), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rdi), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rdi), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 128(%rdi)
	movq	%rsi, 136(%rdi)
	movq	%r8, 144(%rdi)
	movq	%r9, 152(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	96(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	104(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	112(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	120(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 32(%rdi)
	movq	%rsi, 40(%rdi)
	movq	%r8, 48(%rdi)
	movq	%r9, 56(%rdi)
	movq	128(%rsp), %rax
	movq	$121666, %rcx
	mulq	%rcx
	movq	%rax, %r11
	movq	%rdx, %r8
	movq	144(%rsp), %rax
	movq	$121666, %rcx
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	136(%rsp), %rax
	movq	$121666, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	152(%rsp), %rax
	movq	$121666, %rdx
	mulq	%rdx
	movq	%rax, %rax
	movq	%rdx, %rdx
	addq	%rcx, %r8
	adcq	%rsi, %r9
	adcq	%rax, %r10
	adcq	$0, %rdx
	imulq	$38, %rdx, %rax
	addq	%rax, %r11
	adcq	$0, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	movq	$38, %rax
	movq	$0, %rcx
	cmovnbq	%rcx, %rax
	addq	%rax, %r11
	addq	64(%rsp), %r11
	adcq	72(%rsp), %r8
	adcq	80(%rsp), %r9
	adcq	88(%rsp), %r10
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	addq	%rcx, %r11
	adcq	%rax, %r8
	adcq	%rax, %r9
	adcq	%rax, %r10
	cmovbq	%rcx, %rax
	addq	%rax, %r11
	movq	%r11, 64(%rdi)
	movq	%r8, 72(%rdi)
	movq	%r9, 80(%rdi)
	movq	%r10, 88(%rdi)
	movq	$0, %r10
	movq	$0, %rbp
	movq	$0, %rbx
	movq	$0, %r12
	movq	64(%rdi), %rcx
	movq	128(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %rsi
	movq	136(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	144(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	152(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	72(%rdi), %rcx
	movq	128(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	136(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	144(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	152(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	adcq	%rdx, %rbp
	movq	80(%rdi), %rcx
	movq	128(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	136(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	144(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	152(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	adcq	%rdx, %rbx
	movq	88(%rdi), %rcx
	movq	128(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	136(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r11, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	144(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r11, %rbp
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	152(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r11, %rbx
	adcq	%rdx, %r12
	movq	%r10, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rbp, %rax
	movq	%rdx, %r10
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r10
	movq	%rbx, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%r12, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r13
	adcq	%r10, %rsi
	adcq	%r11, %r8
	adcq	%rbp, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r13
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r13
	movq	%r13, 64(%rdi)
	movq	%rsi, 72(%rdi)
	movq	%r8, 80(%rdi)
	movq	%r9, 88(%rdi)
	addq	$224, %rsp
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
