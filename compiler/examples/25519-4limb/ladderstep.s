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
	subq	$416, %rsp
	movq	$121666, (%rsp)
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	(%rdi), %rax
	movq	%rax, (%rsp)
	movq	8(%rdi), %rax
	movq	%rax, 8(%rsp)
	movq	16(%rdi), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rdi), %rax
	movq	%rax, 24(%rsp)
	movq	32(%rdi), %rax
	movq	%rax, 352(%rsp)
	movq	40(%rdi), %rax
	movq	%rax, 360(%rsp)
	movq	48(%rdi), %rax
	movq	%rax, 368(%rsp)
	movq	56(%rdi), %rax
	movq	%rax, 376(%rsp)
	movq	64(%rdi), %rax
	movq	%rax, 384(%rsp)
	movq	72(%rdi), %rax
	movq	%rax, 392(%rsp)
	movq	80(%rdi), %rax
	movq	%rax, 400(%rsp)
	movq	88(%rdi), %rax
	movq	%rax, 408(%rsp)
	movq	96(%rdi), %rax
	movq	%rax, 32(%rsp)
	movq	104(%rdi), %rax
	movq	%rax, 40(%rsp)
	movq	112(%rdi), %rax
	movq	%rax, 48(%rsp)
	movq	120(%rdi), %rax
	movq	%rax, 56(%rsp)
	movq	128(%rdi), %rax
	movq	%rax, 288(%rsp)
	movq	136(%rdi), %rax
	movq	%rax, 296(%rsp)
	movq	144(%rdi), %rax
	movq	%rax, 304(%rsp)
	movq	152(%rdi), %rax
	movq	%rax, 312(%rsp)
	movq	352(%rsp), %rax
	movq	360(%rsp), %rcx
	movq	368(%rsp), %rdx
	movq	376(%rsp), %rsi
	movq	%rax, %r10
	movq	%rcx, %r11
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	addq	384(%rsp), %rax
	adcq	392(%rsp), %rcx
	adcq	400(%rsp), %rdx
	adcq	408(%rsp), %rsi
	movq	$0, %r9
	movq	$38, %r8
	cmovnbq	%r9, %r8
	addq	%r8, %rax
	adcq	%r9, %rcx
	adcq	%r9, %rdx
	adcq	%r9, %rsi
	cmovbq	%r8, %r9
	addq	%r9, %rax
	subq	384(%rsp), %r10
	sbbq	392(%rsp), %r11
	sbbq	400(%rsp), %rbp
	sbbq	408(%rsp), %rbx
	movq	$0, %r9
	movq	$38, %r8
	cmovnbq	%r9, %r8
	subq	%r8, %r10
	sbbq	%r9, %r11
	sbbq	%r9, %rbp
	sbbq	%r9, %rbx
	cmovbq	%r8, %r9
	subq	%r9, %r10
	movq	%rax, 224(%rsp)
	movq	%rcx, 232(%rsp)
	movq	%rdx, 240(%rsp)
	movq	%rsi, 248(%rsp)
	movq	%r10, 160(%rsp)
	movq	%r11, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %r11
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	184(%rsp), %rax
	mulq	160(%rsp)
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
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rax
	movq	%rdx, %rdx
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	$38, %rbx
	movq	%r8, %rax
	mulq	%rbx
	addq	%rax, %r14
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%rbx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r8, %rcx
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r8, %rsi
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	$0, %rbp
	adcq	$0, %rcx
	adcq	$0, %rsi
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	movq	%r14, 320(%rsp)
	movq	%rbp, 328(%rsp)
	movq	%rcx, 336(%rsp)
	movq	%rsi, 344(%rsp)
	movq	$0, %r11
	movq	232(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	240(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	248(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	248(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	248(%rsp), %rax
	mulq	224(%rsp)
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
	movq	224(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	240(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %rax
	movq	%rdx, %rdx
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	248(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	$38, %rbx
	movq	%r8, %rax
	mulq	%rbx
	addq	%rax, %r14
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%rbx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r8, %rcx
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r8, %rsi
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	$0, %rbp
	adcq	$0, %rcx
	adcq	$0, %rsi
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	movq	%r14, 128(%rsp)
	movq	%rbp, 136(%rsp)
	movq	%rcx, 144(%rsp)
	movq	%rsi, 152(%rsp)
	movq	%r14, %rax
	movq	%rbp, %rdx
	movq	%rcx, %rcx
	movq	%rsi, %rsi
	subq	320(%rsp), %rax
	sbbq	328(%rsp), %rdx
	sbbq	336(%rsp), %rcx
	sbbq	344(%rsp), %rsi
	movq	$0, %r9
	movq	$38, %r8
	cmovnbq	%r9, %r8
	subq	%r8, %rax
	sbbq	%r9, %rdx
	sbbq	%r9, %rcx
	sbbq	%r9, %rsi
	cmovbq	%r8, %r9
	subq	%r9, %rax
	movq	%rax, 64(%rsp)
	movq	%rdx, 72(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%rsi, 88(%rsp)
	movq	32(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	56(%rsp), %rsi
	movq	%rax, %r10
	movq	%rcx, %r11
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	addq	288(%rsp), %rax
	adcq	296(%rsp), %rcx
	adcq	304(%rsp), %rdx
	adcq	312(%rsp), %rsi
	movq	$0, %r9
	movq	$38, %r8
	cmovnbq	%r9, %r8
	addq	%r8, %rax
	adcq	%r9, %rcx
	adcq	%r9, %rdx
	adcq	%r9, %rsi
	cmovbq	%r8, %r9
	addq	%r9, %rax
	subq	288(%rsp), %r10
	sbbq	296(%rsp), %r11
	sbbq	304(%rsp), %rbp
	sbbq	312(%rsp), %rbx
	movq	$0, %r9
	movq	$38, %r8
	cmovnbq	%r9, %r8
	subq	%r8, %r10
	sbbq	%r9, %r11
	sbbq	%r9, %rbp
	sbbq	%r9, %rbx
	cmovbq	%r8, %r9
	subq	%r9, %r10
	movq	%rax, 256(%rsp)
	movq	%rcx, 264(%rsp)
	movq	%rdx, 272(%rsp)
	movq	%rsi, 280(%rsp)
	movq	%r10, 192(%rsp)
	movq	%r11, 200(%rsp)
	movq	%rbp, 208(%rsp)
	movq	%rbx, 216(%rsp)
	movq	256(%rsp), %rcx
	movq	160(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	168(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	264(%rsp), %r10
	movq	160(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	168(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	176(%rsp), %rax
	mulq	%r10
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r11, %rcx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	272(%rsp), %r11
	movq	160(%rsp), %rax
	mulq	%r11
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	168(%rsp), %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	176(%rsp), %rax
	mulq	%r11
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbp, %rcx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	280(%rsp), %rbp
	movq	160(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	168(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbx, %rcx
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	184(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%rcx, %rax
	mulq	%rbx
	addq	%rax, %r12
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%rcx, %rsi
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%rcx, %r8
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rcx, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	$0, %rsi
	adcq	$0, %r8
	adcq	$0, %r9
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	movq	%r12, 96(%rsp)
	movq	%rsi, 104(%rsp)
	movq	%r8, 112(%rsp)
	movq	%r9, 120(%rsp)
	movq	192(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	200(%rsp), %r10
	movq	224(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	232(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	240(%rsp), %rax
	mulq	%r10
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r11, %rcx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	208(%rsp), %r11
	movq	224(%rsp), %rax
	mulq	%r11
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	232(%rsp), %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	240(%rsp), %rax
	mulq	%r11
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbp, %rcx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	248(%rsp), %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	216(%rsp), %rbp
	movq	224(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbx, %rcx
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%rcx, %rax
	mulq	%rbx
	addq	%rax, %r12
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%rcx, %rsi
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%rcx, %r8
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rcx, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	$0, %rsi
	adcq	$0, %r8
	adcq	$0, %r9
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	movq	%r12, %rax
	movq	%rsi, %rcx
	movq	%r8, %rdx
	movq	%r9, %r10
	addq	96(%rsp), %rax
	adcq	104(%rsp), %rcx
	adcq	112(%rsp), %rdx
	adcq	120(%rsp), %r10
	movq	$0, %rbp
	movq	$38, %r11
	cmovnbq	%rbp, %r11
	addq	%r11, %rax
	adcq	%rbp, %rcx
	adcq	%rbp, %rdx
	adcq	%rbp, %r10
	cmovbq	%r11, %rbp
	addq	%rbp, %rax
	subq	96(%rsp), %r12
	sbbq	104(%rsp), %rsi
	sbbq	112(%rsp), %r8
	sbbq	120(%rsp), %r9
	movq	$0, %rbp
	movq	$38, %r11
	cmovnbq	%rbp, %r11
	subq	%r11, %r12
	sbbq	%rbp, %rsi
	sbbq	%rbp, %r8
	sbbq	%rbp, %r9
	cmovbq	%r11, %rbp
	subq	%rbp, %r12
	movq	%rax, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%r10, 56(%rsp)
	movq	%r12, 288(%rsp)
	movq	%rsi, 296(%rsp)
	movq	%r8, 304(%rsp)
	movq	%r9, 312(%rsp)
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
	movq	%rax, %rax
	movq	%rdx, %rdx
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
	movq	$38, %rbx
	movq	%r8, %rax
	mulq	%rbx
	addq	%rax, %r14
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%rbx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r8, %rcx
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r8, %rsi
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	$0, %rbp
	adcq	$0, %rcx
	adcq	$0, %rsi
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	movq	%r14, 32(%rsp)
	movq	%rbp, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	%rsi, 56(%rsp)
	movq	$0, %r11
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	adcq	$0, %r8
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	movq	312(%rsp), %rax
	mulq	288(%rsp)
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
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r14
	movq	%rdx, %rbx
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %rax
	movq	%rdx, %rdx
	addq	%rbx, %rbp
	adcq	%r12, %rcx
	adcq	%r13, %rsi
	adcq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	$38, %rbx
	movq	%r8, %rax
	mulq	%rbx
	addq	%rax, %r14
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%rbx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%r8, %rbp
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r8, %rcx
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r8, %rsi
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	adcq	$0, %rbp
	adcq	$0, %rcx
	adcq	$0, %rsi
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r14
	movq	%r14, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%rcx, 304(%rsp)
	movq	%rsi, 312(%rsp)
	movq	288(%rsp), %rcx
	movq	(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r12
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
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	296(%rsp), %r10
	movq	(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	mulq	%r10
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r11, %rcx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	304(%rsp), %r11
	movq	(%rsp), %rax
	mulq	%r11
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	8(%rsp), %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	16(%rsp), %rax
	mulq	%r11
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbp, %rcx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	24(%rsp), %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	312(%rsp), %rbp
	movq	(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	8(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbx, %rcx
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	16(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%rcx, %rax
	mulq	%rbx
	addq	%rax, %r12
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%rcx, %rsi
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%rcx, %r8
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rcx, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	$0, %rsi
	adcq	$0, %r8
	adcq	$0, %r9
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	movq	%r12, 288(%rsp)
	movq	%rsi, 296(%rsp)
	movq	%r8, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rsi
	movq	$0, %r8
	adcq	%rdx, %r8
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r8
	movq	$0, %r9
	adcq	%rdx, %r9
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	136(%rsp), %r10
	movq	320(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	328(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	336(%rsp), %rax
	mulq	%r10
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	344(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r11, %rcx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	144(%rsp), %r11
	movq	320(%rsp), %rax
	mulq	%r11
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	328(%rsp), %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	336(%rsp), %rax
	mulq	%r11
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbp, %rcx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	344(%rsp), %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	152(%rsp), %rbp
	movq	320(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbx, %rcx
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%rcx, %rax
	mulq	%rbx
	addq	%rax, %r12
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%rcx, %rsi
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%rcx, %r8
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rcx, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	$0, %rsi
	adcq	$0, %r8
	adcq	$0, %r9
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	movq	%r12, 352(%rsp)
	movq	%rsi, 360(%rsp)
	movq	%r8, 368(%rsp)
	movq	%r9, 376(%rsp)
	movq	$121666, %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rbp
	movq	%rdx, %r9
	movq	80(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rsi
	movq	%rdx, %r8
	movq	88(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %rax
	addq	%rsi, %r9
	adcq	%r8, %r10
	adcq	%rcx, %r11
	adcq	$0, %rax
	movq	$38, %rcx
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	$38, %rcx
	movq	$0, %rax
	cmovnbq	%rax, %rcx
	addq	%rcx, %rbp
	addq	320(%rsp), %rbp
	adcq	328(%rsp), %r9
	adcq	336(%rsp), %r10
	adcq	344(%rsp), %r11
	movq	$0, %rcx
	movq	$38, %rax
	cmovnbq	%rcx, %rax
	addq	%rax, %rbp
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	cmovbq	%rax, %rcx
	addq	%rcx, %rbp
	movq	%rbp, 384(%rsp)
	movq	%r9, 392(%rsp)
	movq	%r10, 400(%rsp)
	movq	%r11, 408(%rsp)
	movq	384(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r12
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
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	392(%rsp), %r10
	movq	64(%rsp), %rax
	mulq	%r10
	addq	%rax, %rsi
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	%r10
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r11, %r8
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	%r10
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r11, %r9
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%r10
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r11, %rcx
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	400(%rsp), %r11
	movq	64(%rsp), %rax
	mulq	%r11
	addq	%rax, %r8
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	72(%rsp), %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rbp, %r9
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	80(%rsp), %rax
	mulq	%r11
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbp, %rcx
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	88(%rsp), %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbp, %r10
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	408(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%rbx, %rcx
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbp
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%rcx, %rax
	mulq	%rbx
	addq	%rax, %r12
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r10, %rax
	mulq	%rbx
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%rcx, %rsi
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%r11, %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%rcx, %r8
	movq	$0, %rcx
	adcq	%rdx, %rcx
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%rcx, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	$0, %rsi
	adcq	$0, %r8
	adcq	$0, %r9
	movq	$0, %rax
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	movq	%r12, 384(%rsp)
	movq	%rsi, 392(%rsp)
	movq	%r8, 400(%rsp)
	movq	%r9, 408(%rsp)
	movq	352(%rsp), %rax
	movq	%rax, 32(%rdi)
	movq	360(%rsp), %rax
	movq	%rax, 40(%rdi)
	movq	368(%rsp), %rax
	movq	%rax, 48(%rdi)
	movq	376(%rsp), %rax
	movq	%rax, 56(%rdi)
	movq	384(%rsp), %rax
	movq	%rax, 64(%rdi)
	movq	392(%rsp), %rax
	movq	%rax, 72(%rdi)
	movq	400(%rsp), %rax
	movq	%rax, 80(%rdi)
	movq	408(%rsp), %rax
	movq	%rax, 88(%rdi)
	movq	32(%rsp), %rax
	movq	%rax, 96(%rdi)
	movq	40(%rsp), %rax
	movq	%rax, 104(%rdi)
	movq	48(%rsp), %rax
	movq	%rax, 112(%rdi)
	movq	56(%rsp), %rax
	movq	%rax, 120(%rdi)
	movq	288(%rsp), %rax
	movq	%rax, 128(%rdi)
	movq	296(%rsp), %rax
	movq	%rax, 136(%rdi)
	movq	304(%rsp), %rax
	movq	%rax, 144(%rdi)
	movq	312(%rsp), %rax
	movq	%rax, 152(%rdi)
	addq	$416, %rsp
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
