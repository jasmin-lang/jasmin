.text
.p2align 5
.globl _crypto_scalarmult_curve25519_amd64_64_ladderstep
.globl crypto_scalarmult_curve25519_amd64_64_ladderstep
_crypto_scalarmult_curve25519_amd64_64_ladderstep:
crypto_scalarmult_curve25519_amd64_64_ladderstep:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$224, %rsp
	movq	32(%rdi), %rax
	movq	40(%rdi), %rcx
	movq	48(%rdi), %rdx
	movq	56(%rdi), %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	addq	64(%rdi), %rax
	adcq	72(%rdi), %rcx
	adcq	80(%rdi), %rdx
	adcq	88(%rdi), %rsi
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	addq	%rbx, %rax
	adcq	%rbp, %rcx
	adcq	%rbp, %rdx
	adcq	%rbp, %rsi
	cmovbq	%rbx, %rbp
	addq	%rbp, %rax
	subq	64(%rdi), %r8
	sbbq	72(%rdi), %r9
	sbbq	80(%rdi), %r10
	sbbq	88(%rdi), %r11
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	subq	%rbx, %r8
	sbbq	%rbp, %r9
	sbbq	%rbp, %r10
	sbbq	%rbp, %r11
	cmovbq	%rbx, %rbp
	subq	%rbp, %r8
	movq	%rax, (%rsp)
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, 24(%rsp)
	movq	%r8, 32(%rsp)
	movq	%r9, 40(%rsp)
	movq	%r10, 48(%rsp)
	movq	%r11, 56(%rsp)
	movq	$0, %rcx
	movq	40(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	48(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	56(%rsp), %rax
	mulq	48(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	48(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	56(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	56(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	addq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rcx, %rcx
	movq	32(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	40(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	48(%rsp), %rax
	mulq	48(%rsp)
	addq	%r12, %rsi
	adcq	%r13, %r8
	adcq	%r14, %r9
	adcq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	movq	56(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rcx
	movq	%r10, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r10
	movq	%r11, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%rcx, %rax
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rcx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r10, %rbx
	adcq	%r11, %rsi
	adcq	%rbp, %r8
	adcq	%rcx, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 64(%rsp)
	movq	%rsi, 72(%rsp)
	movq	%r8, 80(%rsp)
	movq	%r9, 88(%rsp)
	movq	$0, %rcx
	movq	8(%rsp), %rax
	mulq	(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	16(%rsp), %rax
	mulq	8(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	24(%rsp), %rax
	mulq	16(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	16(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	24(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	24(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	addq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rcx, %rcx
	movq	(%rsp), %rax
	mulq	(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	8(%rsp), %rax
	mulq	8(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	16(%rsp), %rax
	mulq	16(%rsp)
	addq	%r12, %rsi
	adcq	%r13, %r8
	adcq	%r14, %r9
	adcq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	movq	24(%rsp), %rax
	mulq	24(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rcx
	movq	%r10, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r10
	movq	%r11, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%rcx, %rax
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rcx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r10, %rbx
	adcq	%r11, %rsi
	adcq	%rbp, %r8
	adcq	%rcx, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 96(%rsp)
	movq	%rsi, 104(%rsp)
	movq	%r8, 112(%rsp)
	movq	%r9, 120(%rsp)
	movq	%rbx, %rax
	movq	%rsi, %rcx
	movq	%r8, %rdx
	movq	%r9, %rsi
	subq	64(%rsp), %rax
	sbbq	72(%rsp), %rcx
	sbbq	80(%rsp), %rdx
	sbbq	88(%rsp), %rsi
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	subq	%rbx, %rax
	sbbq	%rbp, %rcx
	sbbq	%rbp, %rdx
	sbbq	%rbp, %rsi
	cmovbq	%rbx, %rbp
	subq	%rbp, %rax
	movq	%rax, 128(%rsp)
	movq	%rcx, 136(%rsp)
	movq	%rdx, 144(%rsp)
	movq	%rsi, 152(%rsp)
	movq	96(%rdi), %rax
	movq	104(%rdi), %rcx
	movq	112(%rdi), %rdx
	movq	120(%rdi), %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	addq	128(%rdi), %rax
	adcq	136(%rdi), %rcx
	adcq	144(%rdi), %rdx
	adcq	152(%rdi), %rsi
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	addq	%rbx, %rax
	adcq	%rbp, %rcx
	adcq	%rbp, %rdx
	adcq	%rbp, %rsi
	cmovbq	%rbx, %rbp
	addq	%rbp, %rax
	subq	128(%rdi), %r8
	sbbq	136(%rdi), %r9
	sbbq	144(%rdi), %r10
	sbbq	152(%rdi), %r11
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	subq	%rbx, %r8
	sbbq	%rbp, %r9
	sbbq	%rbp, %r10
	sbbq	%rbp, %r11
	cmovbq	%rbx, %rbp
	subq	%rbp, %r8
	movq	%rax, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rdx, 176(%rsp)
	movq	%rsi, 184(%rsp)
	movq	%r8, 192(%rsp)
	movq	%r9, 200(%rsp)
	movq	%r10, 208(%rsp)
	movq	%r11, 216(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	160(%rsp), %r10
	movq	32(%rsp), %rax
	mulq	%r10
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	40(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	56(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	168(%rsp), %r10
	movq	32(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	40(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r13, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	48(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	56(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	adcq	%rdx, %rsi
	movq	176(%rsp), %r10
	movq	32(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	40(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	48(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	56(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	adcq	%rdx, %r8
	movq	184(%rsp), %r10
	movq	32(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	40(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	48(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	56(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	%rcx, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r8, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r9, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r11
	adcq	%rsi, %rbp
	adcq	%r8, %rbx
	adcq	%r9, %r12
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r11
	movq	%r11, 32(%rsp)
	movq	%rbp, 40(%rsp)
	movq	%rbx, 48(%rsp)
	movq	%r12, 56(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	192(%rsp), %r10
	movq	(%rsp), %rax
	mulq	%r10
	movq	%rax, %r11
	movq	%rdx, %r12
	movq	8(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	16(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	24(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	%rdx, %rcx
	movq	200(%rsp), %r10
	movq	(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	adcq	$0, %rdx
	addq	%r13, %r14
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	$0, %rdx
	addq	%r13, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	adcq	%rdx, %rsi
	movq	208(%rsp), %r10
	movq	(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	$0, %rdx
	addq	%r13, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	adcq	%rdx, %r8
	movq	216(%rsp), %r10
	movq	(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	%rcx, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r8, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r9, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r11
	adcq	%rsi, %r12
	adcq	%r8, %r14
	adcq	%r9, %r15
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rcx, %r12
	adcq	%rcx, %r14
	adcq	%rcx, %r15
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r11
	movq	%r11, %rax
	movq	%r12, %rcx
	movq	%r14, %rdx
	movq	%r15, %rsi
	subq	32(%rsp), %rax
	sbbq	40(%rsp), %rcx
	sbbq	48(%rsp), %rdx
	sbbq	56(%rsp), %rsi
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	subq	%rbx, %rax
	sbbq	%rbp, %rcx
	sbbq	%rbp, %rdx
	sbbq	%rbp, %rsi
	cmovbq	%rbx, %rbp
	subq	%rbp, %rax
	addq	32(%rsp), %r11
	adcq	40(%rsp), %r12
	adcq	48(%rsp), %r14
	adcq	56(%rsp), %r15
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	addq	%rbx, %r11
	adcq	%rbp, %r12
	adcq	%rbp, %r14
	adcq	%rbp, %r15
	cmovbq	%rbx, %rbp
	addq	%rbp, %r11
	movq	%r11, 96(%rdi)
	movq	%r12, 104(%rdi)
	movq	%r14, 112(%rdi)
	movq	%r15, 120(%rdi)
	movq	%rax, 128(%rdi)
	movq	%rcx, 136(%rdi)
	movq	%rdx, 144(%rdi)
	movq	%rsi, 152(%rdi)
	movq	$0, %rcx
	movq	104(%rdi), %rax
	mulq	96(%rdi)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	112(%rdi), %rax
	mulq	104(%rdi)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	120(%rdi), %rax
	mulq	112(%rdi)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	112(%rdi), %rax
	mulq	96(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	120(%rdi), %rax
	mulq	104(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	120(%rdi), %rax
	mulq	96(%rdi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	addq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rcx, %rcx
	movq	96(%rdi), %rax
	mulq	96(%rdi)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	104(%rdi), %rax
	mulq	104(%rdi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	112(%rdi), %rax
	mulq	112(%rdi)
	addq	%r12, %rsi
	adcq	%r13, %r8
	adcq	%r14, %r9
	adcq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	movq	120(%rdi), %rax
	mulq	120(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rcx
	movq	%r10, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r10
	movq	%r11, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%rcx, %rax
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rcx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r10, %rbx
	adcq	%r11, %rsi
	adcq	%rbp, %r8
	adcq	%rcx, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 96(%rdi)
	movq	%rsi, 104(%rdi)
	movq	%r8, 112(%rdi)
	movq	%r9, 120(%rdi)
	movq	$0, %rcx
	movq	136(%rdi), %rax
	mulq	128(%rdi)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	144(%rdi), %rax
	mulq	136(%rdi)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	152(%rdi), %rax
	mulq	144(%rdi)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	144(%rdi), %rax
	mulq	128(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	152(%rdi), %rax
	mulq	136(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	152(%rdi), %rax
	mulq	128(%rdi)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	addq	%rsi, %rsi
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rcx, %rcx
	movq	128(%rdi), %rax
	mulq	128(%rdi)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	136(%rdi), %rax
	mulq	136(%rdi)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	144(%rdi), %rax
	mulq	144(%rdi)
	addq	%r12, %rsi
	adcq	%r13, %r8
	adcq	%r14, %r9
	adcq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	adcq	$0, %rcx
	movq	152(%rdi), %rax
	mulq	152(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rcx
	movq	%r10, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %r10
	movq	%r11, %rax
	movq	%rdx, %r11
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r11
	movq	%rbp, %rax
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rbp
	movq	%rcx, %rax
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rcx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r10, %rbx
	adcq	%r11, %rsi
	adcq	%rbp, %r8
	adcq	%rcx, %r9
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 128(%rdi)
	movq	%rsi, 136(%rdi)
	movq	%r8, 144(%rdi)
	movq	%r9, 152(%rdi)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	128(%rdi), %r10
	movq	(%rdi), %rax
	mulq	%r10
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	8(%rdi), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rdi), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	24(%rdi), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	136(%rdi), %r10
	movq	(%rdi), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rdi), %rax
	mulq	%r10
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r13, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rdi), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rdi), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	adcq	%rdx, %rsi
	movq	144(%rdi), %r10
	movq	(%rdi), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rdi), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rdi), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rdi), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	adcq	%rdx, %r8
	movq	152(%rdi), %r10
	movq	(%rdi), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	8(%rdi), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rdi), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	24(%rdi), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	%rcx, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r8, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r9, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r11
	adcq	%rsi, %rbp
	adcq	%r8, %rbx
	adcq	%r9, %r12
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r11
	movq	%r11, 128(%rdi)
	movq	%rbp, 136(%rdi)
	movq	%rbx, 144(%rdi)
	movq	%r12, 152(%rdi)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	96(%rsp), %r10
	movq	64(%rsp), %rax
	mulq	%r10
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	72(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r12
	adcq	%rdx, %r12
	movq	88(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	104(%rsp), %r10
	movq	64(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbp
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	adcq	$0, %rdx
	addq	%r13, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	adcq	%rdx, %rsi
	movq	112(%rsp), %r10
	movq	64(%rsp), %rax
	mulq	%r10
	addq	%rax, %rbx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%r13, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	adcq	%rdx, %r8
	movq	120(%rsp), %r10
	movq	64(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	%rcx, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r8, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r9, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r11
	adcq	%rsi, %rbp
	adcq	%r8, %rbx
	adcq	%r9, %r12
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r11
	movq	%r11, 32(%rdi)
	movq	%rbp, 40(%rdi)
	movq	%rbx, 48(%rdi)
	movq	%r12, 56(%rdi)
	movq	128(%rsp), %rax
	movq	$121666, %rdx
	mulq	%rdx
	movq	%rax, %r11
	movq	%rdx, %r12
	movq	144(%rsp), %rax
	movq	$121666, %rdx
	mulq	%rdx
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	136(%rsp), %rax
	movq	$121666, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	152(%rsp), %rax
	movq	$121666, %rdx
	mulq	%rdx
	movq	%rax, %rax
	movq	%rdx, %rdx
	addq	%rcx, %r12
	adcq	%rsi, %r14
	adcq	%rax, %r15
	adcq	$0, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r11
	adcq	$0, %r12
	adcq	$0, %r14
	adcq	$0, %r15
	movq	$38, %rcx
	movq	$0, %rsi
	cmovnbq	%rsi, %rcx
	addq	%rcx, %r11
	addq	64(%rsp), %r11
	adcq	72(%rsp), %r12
	adcq	80(%rsp), %r14
	adcq	88(%rsp), %r15
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	addq	%rbx, %r11
	adcq	%rbp, %r12
	adcq	%rbp, %r14
	adcq	%rbp, %r15
	cmovbq	%rbx, %rbp
	addq	%rbp, %r11
	movq	%r11, 64(%rdi)
	movq	%r12, 72(%rdi)
	movq	%r14, 80(%rdi)
	movq	%r15, 88(%rdi)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	64(%rdi), %r10
	movq	128(%rsp), %rax
	mulq	%r10
	movq	%rax, %r11
	movq	%rdx, %r12
	movq	136(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	144(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	152(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	%rdx, %rcx
	movq	72(%rdi), %r10
	movq	128(%rsp), %rax
	mulq	%r10
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	adcq	$0, %rdx
	addq	%r13, %r14
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	$0, %rdx
	addq	%r13, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	adcq	%rdx, %rsi
	movq	80(%rdi), %r10
	movq	128(%rsp), %rax
	mulq	%r10
	addq	%rax, %r14
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	adcq	$0, %rdx
	addq	%r13, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	adcq	%rdx, %r8
	movq	88(%rdi), %r10
	movq	128(%rsp), %rax
	mulq	%r10
	addq	%rax, %r15
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	%rcx, %rax
	movq	$38, %rdx
	mulq	%rdx
	movq	%rax, %rcx
	movq	%rsi, %rax
	movq	%rdx, %rsi
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %rsi
	movq	%r8, %rax
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r8
	movq	%r9, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	$38, %rdx
	mulq	%rdx
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r11
	adcq	%rsi, %r12
	adcq	%r8, %r14
	adcq	%r9, %r15
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rcx, %r12
	adcq	%rcx, %r14
	adcq	%rcx, %r15
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r11
	movq	%r11, 64(%rdi)
	movq	%r12, 72(%rdi)
	movq	%r14, 80(%rdi)
	movq	%r15, 88(%rdi)
	addq	$224, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
  popq  %rbp
	ret 
