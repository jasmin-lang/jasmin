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
	movq	%r10, %rax
	movq	%r11, %rcx
	movq	%rbp, %rdx
	movq	%rbx, %rsi
	movq	%r12, %r8
	movq	$4503599627370458, %r9
	leaq	(%rax,%r9), %r9
	movq	$4503599627370494, %rax
	leaq	(%rcx,%rax), %rcx
	movq	$4503599627370494, %rax
	leaq	(%rdx,%rax), %rdx
	movq	$4503599627370494, %rax
	leaq	(%rsi,%rax), %rsi
	movq	$4503599627370494, %rax
	leaq	(%r8,%rax), %rax
	addq	80(%rdi), %r10
	addq	88(%rdi), %r11
	addq	96(%rdi), %rbp
	addq	104(%rdi), %rbx
	addq	112(%rdi), %r12
	subq	80(%rdi), %r9
	subq	88(%rdi), %rcx
	subq	96(%rdi), %rdx
	subq	104(%rdi), %rsi
	subq	112(%rdi), %rax
	movq	%r10, (%rsp)
	movq	%r11, 8(%rsp)
	movq	%rbp, 16(%rsp)
	movq	%rbx, 24(%rsp)
	movq	%r12, 32(%rsp)
	movq	%r9, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	%rdx, 56(%rsp)
	movq	%rsi, 64(%rsp)
	movq	%rax, 72(%rsp)
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
	leaq	(%r12,%rbx), %rdx
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	leaq	(%rcx,%r13), %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	leaq	(%r8,%rsi), %rsi
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %r8
	imulq	$19, %r11, %r11
	leaq	(%rbp,%r11), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	leaq	(%r9,%rdx), %rdx
	andq	%rax, %r10
	movq	%rdx, %r9
	shrq	$51, %rdx
	leaq	(%rdx,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, %rdx
	shrq	$51, %rcx
	leaq	(%rcx,%rsi), %rcx
	andq	%rax, %rdx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	leaq	(%rcx,%r8), %rcx
	andq	%rax, %rsi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r8
	movq	%rcx, 80(%rsp)
	movq	%r9, 88(%rsp)
	movq	%rdx, 96(%rsp)
	movq	%rsi, 104(%rsp)
	movq	%r8, 112(%rsp)
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
	leaq	(%r12,%rbx), %rdx
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	leaq	(%rcx,%r13), %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	leaq	(%r8,%rsi), %rsi
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %r8
	imulq	$19, %r11, %r11
	leaq	(%rbp,%r11), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	leaq	(%r9,%rdx), %rdx
	andq	%rax, %r10
	movq	%rdx, %r9
	shrq	$51, %rdx
	leaq	(%rdx,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, %rdx
	shrq	$51, %rcx
	leaq	(%rcx,%rsi), %rcx
	andq	%rax, %rdx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	leaq	(%rcx,%r8), %rcx
	andq	%rax, %rsi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r8
	movq	%rcx, 120(%rsp)
	movq	%r9, 128(%rsp)
	movq	%rdx, 136(%rsp)
	movq	%rsi, 144(%rsp)
	movq	%r8, 152(%rsp)
	movq	%rcx, %rax
	movq	%r9, %rcx
	movq	$4503599627370458, %r9
	leaq	(%rax,%r9), %r9
	movq	$4503599627370494, %rax
	leaq	(%rcx,%rax), %rcx
	movq	$4503599627370494, %rax
	leaq	(%rdx,%rax), %rdx
	movq	$4503599627370494, %rax
	leaq	(%rsi,%rax), %rsi
	movq	$4503599627370494, %rax
	leaq	(%r8,%rax), %rax
	subq	80(%rsp), %r9
	subq	88(%rsp), %rcx
	subq	96(%rsp), %rdx
	subq	104(%rsp), %rsi
	subq	112(%rsp), %rax
	movq	%r9, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rdx, 176(%rsp)
	movq	%rsi, 184(%rsp)
	movq	%rax, 192(%rsp)
	movq	120(%rdi), %r10
	movq	128(%rdi), %r11
	movq	136(%rdi), %rbp
	movq	144(%rdi), %rbx
	movq	152(%rdi), %r12
	movq	%r10, %rax
	movq	%r11, %rcx
	movq	%rbp, %rdx
	movq	%rbx, %rsi
	movq	%r12, %r8
	movq	$4503599627370458, %r9
	leaq	(%rax,%r9), %r9
	movq	$4503599627370494, %rax
	leaq	(%rcx,%rax), %rcx
	movq	$4503599627370494, %rax
	leaq	(%rdx,%rax), %rdx
	movq	$4503599627370494, %rax
	leaq	(%rsi,%rax), %rsi
	movq	$4503599627370494, %rax
	leaq	(%r8,%rax), %rax
	addq	160(%rdi), %r10
	addq	168(%rdi), %r11
	addq	176(%rdi), %rbp
	addq	184(%rdi), %rbx
	addq	192(%rdi), %r12
	subq	160(%rdi), %r9
	subq	168(%rdi), %rcx
	subq	176(%rdi), %rdx
	subq	184(%rdi), %rsi
	subq	192(%rdi), %rax
	movq	%r10, 200(%rsp)
	movq	%r11, 208(%rsp)
	movq	%rbp, 216(%rsp)
	movq	%rbx, 224(%rsp)
	movq	%r12, 232(%rsp)
	movq	%r9, 240(%rsp)
	movq	%rcx, 248(%rsp)
	movq	%rdx, 256(%rsp)
	movq	%rsi, 264(%rsp)
	movq	%rax, 272(%rsp)
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
	leaq	(%r8,%rsi), %rdx
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rsi
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %r8
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %r9
	imulq	$19, %r13, %r13
	leaq	(%rcx,%r13), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r8), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%rsi, 56(%rsp)
	movq	%r8, 64(%rsp)
	movq	%r9, 72(%rsp)
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
	leaq	(%r8,%rsi), %rdx
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rsi
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %r8
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %r9
	imulq	$19, %r13, %r13
	leaq	(%rcx,%r13), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r8), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %r12
	andq	%rax, %r9
	movq	%r12, %rax
	movq	%rdx, %rcx
	movq	%rsi, %r10
	movq	%r8, %r11
	movq	%r9, %rbp
	movq	$4503599627370458, %rbx
	leaq	(%rax,%rbx), %rbx
	movq	$4503599627370494, %rax
	leaq	(%rcx,%rax), %rcx
	movq	$4503599627370494, %rax
	leaq	(%r10,%rax), %r10
	movq	$4503599627370494, %rax
	leaq	(%r11,%rax), %r11
	movq	$4503599627370494, %rax
	leaq	(%rbp,%rax), %rax
	addq	40(%rsp), %r12
	addq	48(%rsp), %rdx
	addq	56(%rsp), %rsi
	addq	64(%rsp), %r8
	addq	72(%rsp), %r9
	subq	40(%rsp), %rbx
	subq	48(%rsp), %rcx
	subq	56(%rsp), %r10
	subq	64(%rsp), %r11
	subq	72(%rsp), %rax
	movq	%r12, 120(%rdi)
	movq	%rdx, 128(%rdi)
	movq	%rsi, 136(%rdi)
	movq	%r8, 144(%rdi)
	movq	%r9, 152(%rdi)
	movq	%rbx, 160(%rdi)
	movq	%rcx, 168(%rdi)
	movq	%r10, 176(%rdi)
	movq	%r11, 184(%rdi)
	movq	%rax, 192(%rdi)
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
	leaq	(%r12,%rbx), %rdx
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	leaq	(%rcx,%r13), %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	leaq	(%r8,%rsi), %rsi
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %r8
	imulq	$19, %r11, %r11
	leaq	(%rbp,%r11), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	leaq	(%r9,%rdx), %rdx
	andq	%rax, %r10
	movq	%rdx, %r9
	shrq	$51, %rdx
	leaq	(%rdx,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, %rdx
	shrq	$51, %rcx
	leaq	(%rcx,%rsi), %rcx
	andq	%rax, %rdx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	leaq	(%rcx,%r8), %rcx
	andq	%rax, %rsi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r8
	movq	%rcx, 120(%rdi)
	movq	%r9, 128(%rdi)
	movq	%rdx, 136(%rdi)
	movq	%rsi, 144(%rdi)
	movq	%r8, 152(%rdi)
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
	leaq	(%r12,%rbx), %rdx
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	leaq	(%rcx,%r13), %rcx
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	leaq	(%r8,%rsi), %rsi
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %r8
	imulq	$19, %r11, %r11
	leaq	(%rbp,%r11), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	leaq	(%r9,%rdx), %rdx
	andq	%rax, %r10
	movq	%rdx, %r9
	shrq	$51, %rdx
	leaq	(%rdx,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, %rdx
	shrq	$51, %rcx
	leaq	(%rcx,%rsi), %rcx
	andq	%rax, %rdx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	leaq	(%rcx,%r8), %rcx
	andq	%rax, %rsi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r8
	movq	%rcx, 160(%rdi)
	movq	%r9, 168(%rdi)
	movq	%rdx, 176(%rdi)
	movq	%rsi, 184(%rdi)
	movq	%r8, 192(%rdi)
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
	leaq	(%r8,%rsi), %rdx
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rsi
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %r8
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %r9
	imulq	$19, %r13, %r13
	leaq	(%rcx,%r13), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r8), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, 160(%rdi)
	movq	%rdx, 168(%rdi)
	movq	%rsi, 176(%rdi)
	movq	%r8, 184(%rdi)
	movq	%r9, 192(%rdi)
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
	leaq	(%r8,%rsi), %rdx
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rsi
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %r8
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %r9
	imulq	$19, %r13, %r13
	leaq	(%rcx,%r13), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r8), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, 40(%rdi)
	movq	%rdx, 48(%rdi)
	movq	%rsi, 56(%rdi)
	movq	%r8, 64(%rdi)
	movq	%r9, 72(%rdi)
	movq	160(%rsp), %rax
	movq	$996687872, %rcx
	mulq	%rcx
	shrq	$13, %rax
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	168(%rsp), %rax
	movq	$996687872, %rdx
	mulq	%rdx
	shrq	$13, %rax
	leaq	(%rsi,%rax), %r8
	movq	%rdx, %rsi
	movq	176(%rsp), %rax
	movq	$996687872, %rdx
	mulq	%rdx
	shrq	$13, %rax
	leaq	(%rsi,%rax), %r9
	movq	%rdx, %rsi
	movq	184(%rsp), %rax
	movq	$996687872, %rdx
	mulq	%rdx
	shrq	$13, %rax
	leaq	(%rsi,%rax), %r10
	movq	%rdx, %rsi
	movq	192(%rsp), %rax
	movq	$996687872, %rdx
	mulq	%rdx
	shrq	$13, %rax
	leaq	(%rsi,%rax), %rsi
	imulq	$19, %rdx, %rdx
	leaq	(%rcx,%rdx), %rax
	addq	80(%rsp), %rax
	addq	88(%rsp), %r8
	addq	96(%rsp), %r9
	addq	104(%rsp), %r10
	addq	112(%rsp), %rsi
	movq	%rax, 80(%rdi)
	movq	%r8, 88(%rdi)
	movq	%r9, 96(%rdi)
	movq	%r10, 104(%rdi)
	movq	%rsi, 112(%rdi)
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
	leaq	(%r8,%rsi), %rdx
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	leaq	(%r10,%r9), %rsi
	shldq	$13, %rbp, %rbx
	andq	%rax, %rbp
	leaq	(%rbp,%r11), %r8
	shldq	$13, %r12, %r13
	andq	%rax, %r12
	leaq	(%r12,%rbx), %r9
	imulq	$19, %r13, %r13
	leaq	(%rcx,%r13), %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rdx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	leaq	(%rcx,%rsi), %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	leaq	(%rcx,%r8), %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	leaq	(%rcx,%r9), %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	leaq	(%r10,%rcx), %rcx
	andq	%rax, %r9
	movq	%rcx, 80(%rdi)
	movq	%rdx, 88(%rdi)
	movq	%rsi, 96(%rdi)
	movq	%r8, 104(%rdi)
	movq	%r9, 112(%rdi)
	addq	$296, %rsp
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
