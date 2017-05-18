	.text
	.p2align	5
	.globl	_crypto_scalarmult_curve25519_amd64_51_ladderstep
	.globl	crypto_scalarmult_curve25519_amd64_51_ladderstep
_crypto_scalarmult_curve25519_amd64_51_ladderstep:
crypto_scalarmult_curve25519_amd64_51_ladderstep:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	subq	$296, %rsp
	movq	40(%rdi), %r10
	movq	48(%rdi), %r11
	movq	56(%rdi), %rbp
	movq	64(%rdi), %rbx
	movq	72(%rdi), %r12
	movq	%r10, %rcx
	movq	%r11, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %r8
	movq	%r12, %r9
	movq	$4503599627370458, %rax
	addq	%rax, %rcx
	movq	$4503599627370494, %rax
	addq	%rax, %rdx
	movq	$4503599627370494, %rax
	addq	%rax, %rsi
	movq	$4503599627370494, %rax
	addq	%rax, %r8
	movq	$4503599627370494, %rax
	addq	%rax, %r9
	addq	80(%rdi), %r10
	addq	88(%rdi), %r11
	addq	96(%rdi), %rbp
	addq	104(%rdi), %rbx
	addq	112(%rdi), %r12
	subq	80(%rdi), %rcx
	subq	88(%rdi), %rdx
	subq	96(%rdi), %rsi
	subq	104(%rdi), %r8
	subq	112(%rdi), %r9
	movq	%r10, (%rsp)
	movq	%r11, 8(%rsp)
	movq	%rbp, 16(%rsp)
	movq	%rbx, 24(%rsp)
	movq	%r12, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%rsi, 56(%rsp)
	movq	%r8, 64(%rsp)
	movq	%r9, 72(%rsp)
	movq	40(%rsp), %rax
	mulq	40(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	40(%rsp), %rax
	shlq	$1, %rax
	mulq	48(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	40(%rsp), %rax
	shlq	$1, %rax
	mulq	56(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	40(%rsp), %rax
	shlq	$1, %rax
	mulq	64(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	40(%rsp), %rax
	shlq	$1, %rax
	mulq	72(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	48(%rsp), %rax
	mulq	48(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	48(%rsp), %rax
	shlq	$1, %rax
	mulq	56(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	48(%rsp), %rax
	shlq	$1, %rax
	mulq	64(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	48(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	56(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	56(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	64(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	56(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	64(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	64(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	64(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	72(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	$2251799813685247, %rax
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	addq	%r13, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	imulq	$19, %r11, %rdx
	addq	%rdx, %rbp
	movq	%rbp, %rdx
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rbp
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rbp
	andq	%rax, %r9
	movq	%rbp, 80(%rsp)
	movq	%rsi, 88(%rsp)
	movq	%rcx, 96(%rsp)
	movq	%r8, 104(%rsp)
	movq	%r9, 112(%rsp)
	movq	(%rsp), %rax
	mulq	(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	(%rsp), %rax
	shlq	$1, %rax
	mulq	8(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	(%rsp), %rax
	shlq	$1, %rax
	mulq	16(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	(%rsp), %rax
	shlq	$1, %rax
	mulq	24(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	(%rsp), %rax
	shlq	$1, %rax
	mulq	32(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	8(%rsp), %rax
	shlq	$1, %rax
	mulq	16(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	8(%rsp), %rax
	shlq	$1, %rax
	mulq	24(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	16(%rsp), %rax
	mulq	16(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	16(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	24(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	16(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	24(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	24(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	32(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	$2251799813685247, %rax
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	addq	%r13, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	imulq	$19, %r11, %rdx
	addq	%rdx, %rbp
	movq	%rbp, %rdx
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rbp
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rbp
	andq	%rax, %r9
	movq	%rbp, 120(%rsp)
	movq	%rsi, 128(%rsp)
	movq	%rcx, 136(%rsp)
	movq	%r8, 144(%rsp)
	movq	%r9, 152(%rsp)
	movq	%rbp, %rdx
	movq	%rsi, %rsi
	movq	%rcx, %rcx
	movq	%r8, %r8
	movq	%r9, %r9
	movq	$4503599627370458, %rax
	addq	%rax, %rdx
	movq	$4503599627370494, %rax
	addq	%rax, %rsi
	movq	$4503599627370494, %rax
	addq	%rax, %rcx
	movq	$4503599627370494, %rax
	addq	%rax, %r8
	movq	$4503599627370494, %rax
	addq	%rax, %r9
	subq	80(%rsp), %rdx
	subq	88(%rsp), %rsi
	subq	96(%rsp), %rcx
	subq	104(%rsp), %r8
	subq	112(%rsp), %r9
	movq	%rdx, 160(%rsp)
	movq	%rsi, 168(%rsp)
	movq	%rcx, 176(%rsp)
	movq	%r8, 184(%rsp)
	movq	%r9, 192(%rsp)
	movq	120(%rdi), %r10
	movq	128(%rdi), %r11
	movq	136(%rdi), %rbp
	movq	144(%rdi), %rbx
	movq	152(%rdi), %r12
	movq	%r10, %rcx
	movq	%r11, %rdx
	movq	%rbp, %rsi
	movq	%rbx, %r8
	movq	%r12, %r9
	movq	$4503599627370458, %rax
	addq	%rax, %rcx
	movq	$4503599627370494, %rax
	addq	%rax, %rdx
	movq	$4503599627370494, %rax
	addq	%rax, %rsi
	movq	$4503599627370494, %rax
	addq	%rax, %r8
	movq	$4503599627370494, %rax
	addq	%rax, %r9
	addq	160(%rdi), %r10
	addq	168(%rdi), %r11
	addq	176(%rdi), %rbp
	addq	184(%rdi), %rbx
	addq	192(%rdi), %r12
	subq	160(%rdi), %rcx
	subq	168(%rdi), %rdx
	subq	176(%rdi), %rsi
	subq	184(%rdi), %r8
	subq	192(%rdi), %r9
	movq	%r10, 200(%rsp)
	movq	%r11, 208(%rsp)
	movq	%rbp, 216(%rsp)
	movq	%rbx, 224(%rsp)
	movq	%r12, 232(%rsp)
	movq	%rcx, 240(%rsp)
	movq	%rdx, 248(%rsp)
	movq	%rsi, 256(%rsp)
	movq	%r8, 264(%rsp)
	movq	%r9, 272(%rsp)
	movq	224(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 280(%rsp)
	mulq	56(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	232(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 288(%rsp)
	mulq	48(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	200(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	200(%rsp), %rax
	mulq	48(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	200(%rsp), %rax
	mulq	56(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	200(%rsp), %rax
	mulq	64(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	200(%rsp), %rax
	mulq	72(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	208(%rsp), %rax
	mulq	48(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	208(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	208(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	216(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	216(%rsp), %rax
	mulq	48(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	216(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	64(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	216(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	72(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	224(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	224(%rsp), %rax
	mulq	48(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	280(%rsp), %rax
	mulq	72(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	232(%rsp), %rax
	mulq	40(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	288(%rsp), %rax
	mulq	56(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	288(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	288(%rsp), %rax
	mulq	72(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	addq	%r11, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	imulq	$19, %r13, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r10, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	addq	%r12, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	andq	%rax, %r9
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r10
	movq	%rcx, 40(%rsp)
	movq	%rsi, 48(%rsp)
	movq	%r8, 56(%rsp)
	movq	%r9, 64(%rsp)
	movq	%r10, 72(%rsp)
	movq	264(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 200(%rsp)
	mulq	16(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	272(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 208(%rsp)
	mulq	8(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	240(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	240(%rsp), %rax
	mulq	8(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	240(%rsp), %rax
	mulq	16(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	240(%rsp), %rax
	mulq	24(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	32(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	248(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	248(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	16(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	24(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	248(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	256(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	256(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	256(%rsp), %rax
	mulq	16(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	264(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	8(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	24(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	200(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	16(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	208(%rsp), %rax
	mulq	24(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	208(%rsp), %rax
	mulq	32(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	addq	%r11, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	imulq	$19, %r13, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r10, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	addq	%r12, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	andq	%rax, %r9
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r10
	movq	%rcx, %rdx
	movq	%rsi, %r11
	movq	%r8, %rbp
	movq	%r9, %rbx
	movq	%r10, %r12
	movq	$4503599627370458, %rax
	addq	%rax, %rdx
	movq	$4503599627370494, %rax
	addq	%rax, %r11
	movq	$4503599627370494, %rax
	addq	%rax, %rbp
	movq	$4503599627370494, %rax
	addq	%rax, %rbx
	movq	$4503599627370494, %rax
	addq	%rax, %r12
	addq	40(%rsp), %rcx
	addq	48(%rsp), %rsi
	addq	56(%rsp), %r8
	addq	64(%rsp), %r9
	addq	72(%rsp), %r10
	subq	40(%rsp), %rdx
	subq	48(%rsp), %r11
	subq	56(%rsp), %rbp
	subq	64(%rsp), %rbx
	subq	72(%rsp), %r12
	movq	%rcx, 120(%rdi)
	movq	%rsi, 128(%rdi)
	movq	%r8, 136(%rdi)
	movq	%r9, 144(%rdi)
	movq	%r10, 152(%rdi)
	movq	%rdx, 160(%rdi)
	movq	%r11, 168(%rdi)
	movq	%rbp, 176(%rdi)
	movq	%rbx, 184(%rdi)
	movq	%r12, 192(%rdi)
	movq	120(%rdi), %rax
	mulq	120(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	120(%rdi), %rax
	shlq	$1, %rax
	mulq	128(%rdi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	120(%rdi), %rax
	shlq	$1, %rax
	mulq	136(%rdi)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	120(%rdi), %rax
	shlq	$1, %rax
	mulq	144(%rdi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	120(%rdi), %rax
	shlq	$1, %rax
	mulq	152(%rdi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	128(%rdi), %rax
	mulq	128(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	128(%rdi), %rax
	shlq	$1, %rax
	mulq	136(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	128(%rdi), %rax
	shlq	$1, %rax
	mulq	144(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	128(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	152(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	136(%rdi), %rax
	mulq	136(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	136(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	144(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	136(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	152(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	144(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	144(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	144(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	152(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	152(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	152(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	$2251799813685247, %rax
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	addq	%r13, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	imulq	$19, %r11, %rdx
	addq	%rdx, %rbp
	movq	%rbp, %rdx
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rbp
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rbp
	andq	%rax, %r9
	movq	%rbp, 120(%rdi)
	movq	%rsi, 128(%rdi)
	movq	%rcx, 136(%rdi)
	movq	%r8, 144(%rdi)
	movq	%r9, 152(%rdi)
	movq	160(%rdi), %rax
	mulq	160(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	160(%rdi), %rax
	shlq	$1, %rax
	mulq	168(%rdi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	160(%rdi), %rax
	shlq	$1, %rax
	mulq	176(%rdi)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	160(%rdi), %rax
	shlq	$1, %rax
	mulq	184(%rdi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	160(%rdi), %rax
	shlq	$1, %rax
	mulq	192(%rdi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	168(%rdi), %rax
	mulq	168(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	168(%rdi), %rax
	shlq	$1, %rax
	mulq	176(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	168(%rdi), %rax
	shlq	$1, %rax
	mulq	184(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	168(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	192(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	176(%rdi), %rax
	mulq	176(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	176(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	184(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	176(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	192(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	184(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	184(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	184(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	192(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	192(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	192(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	$2251799813685247, %rax
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	addq	%r13, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	imulq	$19, %r11, %rdx
	addq	%rdx, %rbp
	movq	%rbp, %rdx
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rbp
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rbp
	andq	%rax, %r9
	movq	%rbp, 160(%rdi)
	movq	%rsi, 168(%rdi)
	movq	%rcx, 176(%rdi)
	movq	%r8, 184(%rdi)
	movq	%r9, 192(%rdi)
	movq	184(%rdi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, (%rsp)
	mulq	16(%rdi)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	192(%rdi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	8(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	160(%rdi), %rax
	mulq	(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	160(%rdi), %rax
	mulq	8(%rdi)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	160(%rdi), %rax
	mulq	16(%rdi)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	160(%rdi), %rax
	mulq	24(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	160(%rdi), %rax
	mulq	32(%rdi)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	168(%rdi), %rax
	mulq	(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	168(%rdi), %rax
	mulq	8(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	168(%rdi), %rax
	mulq	16(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	168(%rdi), %rax
	mulq	24(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	168(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	176(%rdi), %rax
	mulq	(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	176(%rdi), %rax
	mulq	8(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	176(%rdi), %rax
	mulq	16(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	176(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	176(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	184(%rdi), %rax
	mulq	(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	184(%rdi), %rax
	mulq	8(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	(%rsp), %rax
	mulq	24(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	(%rsp), %rax
	mulq	32(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	192(%rdi), %rax
	mulq	(%rdi)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	16(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	8(%rsp), %rax
	mulq	24(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	32(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	addq	%r11, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	imulq	$19, %r13, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r10, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	addq	%r12, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	andq	%rax, %r9
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r10
	movq	%rcx, 160(%rdi)
	movq	%rsi, 168(%rdi)
	movq	%r8, 176(%rdi)
	movq	%r9, 184(%rdi)
	movq	%r10, 192(%rdi)
	movq	144(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, (%rsp)
	mulq	96(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	152(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	88(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	120(%rsp), %rax
	mulq	80(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	120(%rsp), %rax
	mulq	88(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	120(%rsp), %rax
	mulq	96(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	120(%rsp), %rax
	mulq	104(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	120(%rsp), %rax
	mulq	112(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	128(%rsp), %rax
	mulq	80(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	128(%rsp), %rax
	mulq	88(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	128(%rsp), %rax
	mulq	96(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	128(%rsp), %rax
	mulq	104(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	128(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	112(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	136(%rsp), %rax
	mulq	80(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	136(%rsp), %rax
	mulq	88(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	136(%rsp), %rax
	mulq	96(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	104(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	136(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	112(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	144(%rsp), %rax
	mulq	80(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	144(%rsp), %rax
	mulq	88(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	(%rsp), %rax
	mulq	104(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	(%rsp), %rax
	mulq	112(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	152(%rsp), %rax
	mulq	80(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	96(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	8(%rsp), %rax
	mulq	104(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	112(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	addq	%r11, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	imulq	$19, %r13, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r10, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	addq	%r12, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	andq	%rax, %r9
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r10
	movq	%rcx, 40(%rdi)
	movq	%rsi, 48(%rdi)
	movq	%r8, 56(%rdi)
	movq	%r9, 64(%rdi)
	movq	%r10, 72(%rdi)
	movq	160(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	movq	%rax, %r11
	movq	%rdx, %rsi
	movq	168(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %rsi
	movq	%rdx, %r8
	movq	176(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r8
	movq	%rdx, %r9
	movq	184(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r9
	movq	%rdx, %r10
	movq	192(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r10
	imulq	$19, %rdx, %rax
	addq	%rax, %r11
	addq	80(%rsp), %r11
	addq	88(%rsp), %rsi
	addq	96(%rsp), %r8
	addq	104(%rsp), %r9
	addq	112(%rsp), %r10
	movq	%r11, 80(%rdi)
	movq	%rsi, 88(%rdi)
	movq	%r8, 96(%rdi)
	movq	%r9, 104(%rdi)
	movq	%r10, 112(%rdi)
	movq	104(%rdi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, (%rsp)
	mulq	176(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	112(%rdi), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	168(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	80(%rdi), %rax
	mulq	160(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	80(%rdi), %rax
	mulq	168(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	80(%rdi), %rax
	mulq	176(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	80(%rdi), %rax
	mulq	184(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	80(%rdi), %rax
	mulq	192(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	88(%rdi), %rax
	mulq	160(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	88(%rdi), %rax
	mulq	168(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	88(%rdi), %rax
	mulq	176(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	88(%rdi), %rax
	mulq	184(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	88(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	192(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	96(%rdi), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	96(%rdi), %rax
	mulq	168(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	96(%rdi), %rax
	mulq	176(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	96(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	184(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	96(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	192(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	104(%rdi), %rax
	mulq	160(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	104(%rdi), %rax
	mulq	168(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	112(%rdi), %rax
	mulq	160(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	176(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	8(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	8(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rsi, %r8
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%r9, %r10
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	addq	%r11, %rbp
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	addq	%rbx, %r12
	imulq	$19, %r13, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r10, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	addq	%r12, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	andq	%rax, %r9
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r10
	movq	%rcx, 80(%rdi)
	movq	%rsi, 88(%rdi)
	movq	%r8, 96(%rdi)
	movq	%r9, 104(%rdi)
	movq	%r10, 112(%rdi)
	addq	$296, %rsp
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
