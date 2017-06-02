	.text
	.p2align	5
	.globl	_scalarmult
	.globl	scalarmult
_scalarmult:
scalarmult:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$480, %rsp
	movq	(%rsi), %rax
	movq	%rax, (%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 8(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	(%rsi), %rcx
	movq	$-8, %rax
	andq	%rax, %rcx
	movq	%rcx, %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %r10
	movq	$9223372036854775807, %r9
	andq	%r9, %r10
	movq	$4611686018427387904, %r9
	orq 	%r9, %r10
	movq	%r10, %r9
	movq	%rax, (%rsi)
	movq	%rcx, 8(%rsi)
	movq	%r8, 16(%rsi)
	movq	%r9, 24(%rsi)
	movq	(%rdx), %rax
	movq	%rax, 32(%rsp)
	movq	8(%rdx), %rax
	movq	%rax, 40(%rsp)
	movq	16(%rdx), %rax
	movq	%rax, 48(%rsp)
	movq	24(%rdx), %rcx
	movq	$9223372036854775807, %rax
	andq	%rax, %rcx
	movq	%rcx, 56(%rsp)
	movq	32(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	56(%rsp), %r8
	movq	%rax, 64(%rsp)
	movq	%rcx, 72(%rsp)
	movq	%rdx, 80(%rsp)
	movq	%r8, 88(%rsp)
	movq	%rax, 192(%rsp)
	movq	%rcx, 200(%rsp)
	movq	%rdx, 208(%rsp)
	movq	%r8, 216(%rsp)
	movq	$1, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$1, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$62, %rcx
	movq	$3, %rdx
	movq	$0, 152(%rsp)
	jmp 	L15
L16:
L15:
	movq	(%rsi,%rdx,8), %rax
	movq	%rdx, 128(%rsp)
	movq	%rax, 136(%rsp)
	jmp 	L17
L18:
L17:
	movq	136(%rsp), %rax
	shrq	%cl, %rax
	movq	%rcx, 144(%rsp)
	andq	$1, %rax
	movq	152(%rsp), %rcx
	xorq	%rax, %rcx
	movq	%rax, 152(%rsp)
	subq	$1, %rcx
	movq	384(%rsp), %rcx
	movq	160(%rsp), %rdx
	movq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	cmovnbq	%rax, %rdx
	movq	%rcx, 384(%rsp)
	movq	%rdx, 160(%rsp)
	movq	392(%rsp), %rcx
	movq	168(%rsp), %rdx
	movq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	cmovnbq	%rax, %rdx
	movq	%rcx, 392(%rsp)
	movq	%rdx, 168(%rsp)
	movq	400(%rsp), %rcx
	movq	176(%rsp), %rdx
	movq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	cmovnbq	%rax, %rdx
	movq	%rcx, 400(%rsp)
	movq	%rdx, 176(%rsp)
	movq	408(%rsp), %rcx
	movq	184(%rsp), %rdx
	movq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	cmovnbq	%rax, %rdx
	movq	%rcx, 408(%rsp)
	movq	%rdx, 184(%rsp)
	movq	96(%rsp), %rcx
	movq	192(%rsp), %rdx
	movq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	cmovnbq	%rax, %rdx
	movq	%rdx, 192(%rsp)
	movq	104(%rsp), %rdx
	movq	200(%rsp), %r8
	movq	%rdx, %rax
	cmovnbq	%r8, %rdx
	cmovnbq	%rax, %r8
	movq	%r8, 200(%rsp)
	movq	112(%rsp), %r8
	movq	208(%rsp), %r9
	movq	%r8, %rax
	cmovnbq	%r9, %r8
	cmovnbq	%rax, %r9
	movq	%r9, 208(%rsp)
	movq	120(%rsp), %r9
	movq	216(%rsp), %r10
	movq	%r9, %rax
	cmovnbq	%r10, %r9
	cmovnbq	%rax, %r10
	movq	%r10, 216(%rsp)
	movq	%rcx, %r11
	movq	%rdx, %rbp
	movq	%r8, %rbx
	movq	%r9, %r12
	addq	384(%rsp), %rcx
	adcq	392(%rsp), %rdx
	adcq	400(%rsp), %r8
	adcq	408(%rsp), %r9
	movq	$0, %r10
	movq	$38, %rax
	cmovnbq	%r10, %rax
	addq	%rax, %rcx
	adcq	%r10, %rdx
	adcq	%r10, %r8
	adcq	%r10, %r9
	cmovbq	%rax, %r10
	addq	%r10, %rcx
	subq	384(%rsp), %r11
	sbbq	392(%rsp), %rbp
	sbbq	400(%rsp), %rbx
	sbbq	408(%rsp), %r12
	movq	$0, %r10
	movq	$38, %rax
	cmovnbq	%r10, %rax
	subq	%rax, %r11
	sbbq	%r10, %rbp
	sbbq	%r10, %rbx
	sbbq	%r10, %r12
	cmovbq	%rax, %r10
	subq	%r10, %r11
	movq	%rcx, 256(%rsp)
	movq	%rdx, 264(%rsp)
	movq	%r8, 272(%rsp)
	movq	%r9, 280(%rsp)
	movq	%r11, 320(%rsp)
	movq	%rbp, 328(%rsp)
	movq	%rbx, 336(%rsp)
	movq	%r12, 344(%rsp)
	movq	$0, %rbp
	movq	328(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	336(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	344(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	336(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	344(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	344(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	320(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	336(%rsp), %rax
	mulq	336(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	344(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 448(%rsp)
	movq	%r9, 456(%rsp)
	movq	%r14, 464(%rsp)
	movq	%r10, 472(%rsp)
	movq	$0, %rbp
	movq	264(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	280(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	280(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	256(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 416(%rsp)
	movq	%r9, 424(%rsp)
	movq	%r14, 432(%rsp)
	movq	%r10, 440(%rsp)
	movq	%r15, %rax
	movq	%r9, %rcx
	movq	%r14, %rdx
	movq	%r10, %r8
	subq	448(%rsp), %rax
	sbbq	456(%rsp), %rcx
	sbbq	464(%rsp), %rdx
	sbbq	472(%rsp), %r8
	movq	$0, %r10
	movq	$38, %r9
	cmovnbq	%r10, %r9
	subq	%r9, %rax
	sbbq	%r10, %rcx
	sbbq	%r10, %rdx
	sbbq	%r10, %r8
	cmovbq	%r9, %r10
	subq	%r10, %rax
	movq	%rax, 224(%rsp)
	movq	%rcx, 232(%rsp)
	movq	%rdx, 240(%rsp)
	movq	%r8, 248(%rsp)
	movq	192(%rsp), %rax
	movq	200(%rsp), %rcx
	movq	208(%rsp), %rdx
	movq	216(%rsp), %r8
	movq	%rax, %r11
	movq	%rcx, %rbp
	movq	%rdx, %rbx
	movq	%r8, %r12
	addq	160(%rsp), %rax
	adcq	168(%rsp), %rcx
	adcq	176(%rsp), %rdx
	adcq	184(%rsp), %r8
	movq	$0, %r10
	movq	$38, %r9
	cmovnbq	%r10, %r9
	addq	%r9, %rax
	adcq	%r10, %rcx
	adcq	%r10, %rdx
	adcq	%r10, %r8
	cmovbq	%r9, %r10
	addq	%r10, %rax
	subq	160(%rsp), %r11
	sbbq	168(%rsp), %rbp
	sbbq	176(%rsp), %rbx
	sbbq	184(%rsp), %r12
	movq	$0, %r10
	movq	$38, %r9
	cmovnbq	%r10, %r9
	subq	%r9, %r11
	sbbq	%r10, %rbp
	sbbq	%r10, %rbx
	sbbq	%r10, %r12
	cmovbq	%r9, %r10
	subq	%r10, %r11
	movq	%rax, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%r8, 56(%rsp)
	movq	%r11, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%rbx, 304(%rsp)
	movq	%r12, 312(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	32(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	40(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	48(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	56(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 352(%rsp)
	movq	%rbp, 360(%rsp)
	movq	%rbx, 368(%rsp)
	movq	%r12, 376(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, %rax
	movq	%rbp, %rcx
	movq	%rbx, %rdx
	movq	%r12, %r8
	addq	352(%rsp), %rax
	adcq	360(%rsp), %rcx
	adcq	368(%rsp), %rdx
	adcq	376(%rsp), %r8
	movq	$0, %r10
	movq	$38, %r9
	cmovnbq	%r10, %r9
	addq	%r9, %rax
	adcq	%r10, %rcx
	adcq	%r10, %rdx
	adcq	%r10, %r8
	cmovbq	%r9, %r10
	addq	%r10, %rax
	subq	352(%rsp), %r15
	sbbq	360(%rsp), %rbp
	sbbq	368(%rsp), %rbx
	sbbq	376(%rsp), %r12
	movq	$0, %r10
	movq	$38, %r9
	cmovnbq	%r10, %r9
	subq	%r9, %r15
	sbbq	%r10, %rbp
	sbbq	%r10, %rbx
	sbbq	%r10, %r12
	cmovbq	%r9, %r10
	subq	%r10, %r15
	movq	%rax, 192(%rsp)
	movq	%rcx, 200(%rsp)
	movq	%rdx, 208(%rsp)
	movq	%r8, 216(%rsp)
	movq	%r15, 160(%rsp)
	movq	%rbp, 168(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%r12, 184(%rsp)
	movq	$0, %rbp
	movq	200(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	208(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	216(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	208(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	216(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	216(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	192(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	208(%rsp), %rax
	mulq	208(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	216(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 192(%rsp)
	movq	%r9, 200(%rsp)
	movq	%r14, 208(%rsp)
	movq	%r10, 216(%rsp)
	movq	$0, %rbp
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 160(%rsp)
	movq	%r9, 168(%rsp)
	movq	%r14, 176(%rsp)
	movq	%r10, 184(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	160(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	168(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	176(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	184(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 160(%rsp)
	movq	%rbp, 168(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%r12, 184(%rsp)
	movq	$121666, %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rbx
	movq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	232(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	248(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %rax
	addq	%r8, %r10
	adcq	%r9, %r11
	adcq	%rcx, %rbp
	adcq	$0, %rax

	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	$38, %rcx
	movq	$0, %rax
	cmovnbq	%rax, %rcx
	addq	%rcx, %rbx
	addq	448(%rsp), %rbx
	adcq	456(%rsp), %r10
	adcq	464(%rsp), %r11
	adcq	472(%rsp), %rbp
	movq	$0, %rcx
	movq	$38, %rax
	cmovnbq	%rcx, %rax
	addq	%rax, %rbx
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rbp
	cmovbq	%rax, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 384(%rsp)
	movq	%r10, 392(%rsp)
	movq	%r11, 400(%rsp)
	movq	%rbp, 408(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	384(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	392(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	400(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	408(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 384(%rsp)
	movq	%rbp, 392(%rsp)
	movq	%rbx, 400(%rsp)
	movq	%r12, 408(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	416(%rsp), %rcx
	movq	448(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	456(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	464(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	472(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	424(%rsp), %rcx
	movq	448(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	456(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	464(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	472(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	432(%rsp), %rcx
	movq	448(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	456(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	464(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	472(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	440(%rsp), %rcx
	movq	448(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	456(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	464(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	472(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 96(%rsp)
	movq	%rbp, 104(%rsp)
	movq	%rbx, 112(%rsp)
	movq	%r12, 120(%rsp)
	movq	144(%rsp), %rcx
	decq	%rcx
	cmpq	$0, %rcx
	jnl 	L18
	movq	$63, %rcx
	movq	128(%rsp), %rdx
	decq	%rdx
	cmpq	$0, %rdx
	jnl 	L16
	movq	$0, %rbp
	movq	392(%rsp), %rax
	mulq	384(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	400(%rsp), %rax
	mulq	392(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	408(%rsp), %rax
	mulq	400(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	400(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	408(%rsp), %rax
	mulq	392(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	408(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	384(%rsp), %rax
	mulq	384(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	392(%rsp), %rax
	mulq	392(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	400(%rsp), %rax
	mulq	400(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	408(%rsp), %rax
	mulq	408(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 192(%rsp)
	movq	%r9, 200(%rsp)
	movq	%r14, 208(%rsp)
	movq	%r10, 216(%rsp)
	movq	$0, %rbp
	movq	200(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	208(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	216(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	208(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	216(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	216(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	192(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	208(%rsp), %rax
	mulq	208(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	216(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 32(%rsp)
	movq	%rbp, 40(%rsp)
	movq	%rbx, 48(%rsp)
	movq	%r12, 56(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	32(%rsp), %rcx
	movq	192(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	200(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	208(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	216(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	40(%rsp), %rcx
	movq	192(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	200(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	208(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	216(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	48(%rsp), %rcx
	movq	192(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	200(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	208(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	216(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	56(%rsp), %rcx
	movq	192(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	200(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	208(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	216(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 352(%rsp)
	movq	%rbp, 360(%rsp)
	movq	%rbx, 368(%rsp)
	movq	%r12, 376(%rsp)
	movq	$0, %rbp
	movq	360(%rsp), %rax
	mulq	352(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	368(%rsp), %rax
	mulq	360(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	376(%rsp), %rax
	mulq	368(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	368(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	376(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	376(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	352(%rsp), %rax
	mulq	352(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	360(%rsp), %rax
	mulq	360(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	368(%rsp), %rax
	mulq	368(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	376(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	40(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	48(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	56(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 64(%rsp)
	movq	%rbp, 72(%rsp)
	movq	%rbx, 80(%rsp)
	movq	%r12, 88(%rsp)
	movq	$0, %rbp
	movq	72(%rsp), %rax
	mulq	64(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	80(%rsp), %rax
	mulq	72(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	88(%rsp), %rax
	mulq	80(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	88(%rsp), %rax
	mulq	72(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	88(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	64(%rsp), %rax
	mulq	64(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	72(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	80(%rsp), %rax
	mulq	80(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	88(%rsp), %rax
	mulq	88(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$3, 128(%rsp)
	jmp 	L13
L14:
L13:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L14
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	64(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	72(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 224(%rsp)
	movq	%rbp, 232(%rsp)
	movq	%rbx, 240(%rsp)
	movq	%r12, 248(%rsp)
	movq	$0, %rbp
	movq	232(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	240(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	248(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	240(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	248(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	248(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	224(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	232(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	240(%rsp), %rax
	mulq	240(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	248(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$8, 128(%rsp)
	jmp 	L11
L12:
L11:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L12
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 256(%rsp)
	movq	%rbp, 264(%rsp)
	movq	%rbx, 272(%rsp)
	movq	%r12, 280(%rsp)
	movq	$0, %rbp
	movq	264(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	280(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	280(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	256(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$18, 128(%rsp)
	jmp 	L9
L10:
L9:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L10
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	256(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%rbx, 304(%rsp)
	movq	%r12, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$8, 128(%rsp)
	jmp 	L7
L8:
L7:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L8
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	224(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	232(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	248(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 320(%rsp)
	movq	%rbp, 328(%rsp)
	movq	%rbx, 336(%rsp)
	movq	%r12, 344(%rsp)
	movq	$0, %rbp
	movq	328(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	336(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	344(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	336(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	344(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	344(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	320(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	336(%rsp), %rax
	mulq	336(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	344(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$48, 128(%rsp)
	jmp 	L5
L6:
L5:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L6
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 160(%rsp)
	movq	%rbp, 168(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%r12, 184(%rsp)
	movq	$0, %rbp
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$98, 128(%rsp)
	jmp 	L3
L4:
L3:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L4
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	160(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	168(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	160(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	168(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	160(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	168(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	160(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	168(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%rbx, 304(%rsp)
	movq	%r12, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$48, 128(%rsp)
	jmp 	L1
L2:
L1:
	movq	288(%rsp), %rcx
	movq	296(%rsp), %r8
	movq	304(%rsp), %r9
	movq	%r8, %rax
	mulq	%rcx
	movq	%rax, %r13
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r8
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	312(%rsp), %rax
	mulq	%r9
	movq	%rax, %r9
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	304(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	%r8
	addq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	movq	312(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r13, %r13
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r9, %r9
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r14
	movq	%r8, %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r14, %r13
	adcq	%r8, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r9
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12

	movq	$0, %r14
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%r12, %rax
	movq	$0, %r9
	adcq	%rdx, %r9
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %r15
	adcq	%r13, %rbp
	adcq	%r10, %r14
	adcq	%r11, %r9
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %r9
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r9, 312(%rsp)
	movq	128(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 128(%rsp)
	jnb 	L2
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	320(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	328(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	344(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%rbp, 296(%rsp)
	movq	%rbx, 304(%rsp)
	movq	%r12, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rbp
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	adcq	$0, %r9
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	addq	%rbx, %rbx
	adcq	%rcx, %rcx
	adcq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r13, %rbx
	adcq	%r14, %rcx
	adcq	%r15, %r8
	adcq	%rax, %r9
	adcq	%rdx, %r10
	adcq	$0, %r11
	adcq	$0, %rbp
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp

	movq	$0, %r14
	movq	%r9, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %r9
	movq	%r10, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r9
	movq	%r11, %rax
	adcq	%rdx, %r14
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r14
	movq	%rbp, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r15
	adcq	%rbx, %r9
	adcq	%rcx, %r14
	adcq	%r8, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r14, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	288(%rsp), %rcx
	movq	352(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	360(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	368(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	376(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	296(%rsp), %rcx
	movq	352(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	360(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	376(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	304(%rsp), %rcx
	movq	352(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	360(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	376(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	312(%rsp), %rcx
	movq	352(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	360(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	376(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, 384(%rsp)
	movq	%rbp, 392(%rsp)
	movq	%rbx, 400(%rsp)
	movq	%r12, 408(%rsp)
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r13
	movq	$0, %r14
	movq	96(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	adcq	%rdx, %r10
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	104(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r9
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	adcq	%rdx, %r12
	movq	112(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%rbx, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	adcq	%rdx, %r13
	movq	120(%rsp), %rcx
	movq	384(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	392(%rsp), %rax
	mulq	%rcx
	addq	%rax, %rbp
	adcq	$0, %rdx
	addq	%rbx, %rbp
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	400(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r12
	adcq	$0, %rdx
	addq	%rbx, %r12
	movq	$0, %rbx
	adcq	%rdx, %rbx
	movq	408(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%rbx, %r13
	adcq	%rdx, %r14

	movq	$0, %rbx
	movq	%rbp, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	movq	%rax, %r15
	movq	%rdx, %rbp
	movq	%r12, %rax
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbp
	movq	%r13, %rax
	adcq	%rdx, %rbx
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %rbx
	movq	%r14, %rax
	movq	$0, %r12
	adcq	%rdx, %r12
	mulq	crypto_scalarmult_curve25519_amd64_64_38
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %r15
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r15
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r15
	movq	%r15, %r10
	movq	%rbp, %r11
	movq	%rbx, %rbp
	movq	%r12, %rbx
	movq	%r10, %rcx
	movq	%r11, %rdx
	movq	%rbp, %r8
	movq	%rbx, %r9
	movq	$1, %rax
	shlq	$63, %rax
	addq	$19, %rcx
	adcq	$0, %rdx
	adcq	$0, %r8
	adcq	%rax, %r9
	cmovbq	%rcx, %r10
	cmovbq	%rdx, %r11
	cmovbq	%r8, %rbp
	cmovbq	%r9, %rbx
	movq	%r10, %rcx
	movq	%r11, %rdx
	movq	%rbp, %r8
	movq	%rbx, %r9
	addq	$19, %rcx
	adcq	$0, %rdx
	adcq	$0, %r8
	adcq	%rax, %r9
	cmovbq	%rcx, %r10
	cmovbq	%rdx, %r11
	cmovbq	%r8, %rbp
	cmovbq	%r9, %rbx
	movq	%r10, %rax
	movq	%r11, %rcx
	movq	%rbp, %rdx
	movq	%rbx, %r8
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%r8, 24(%rdi)
	movq	(%rsp), %rax
	movq	%rax, (%rsi)
	movq	8(%rsp), %rax
	movq	%rax, 8(%rsi)
	movq	16(%rsp), %rax
	movq	%rax, 16(%rsi)
	movq	24(%rsp), %rax
	movq	%rax, 24(%rsi)
	addq	$480, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 

.data

.globl crypto_scalarmult_curve25519_amd64_64_121666
.globl crypto_scalarmult_curve25519_amd64_64_MU0
.globl crypto_scalarmult_curve25519_amd64_64_MU1
.globl crypto_scalarmult_curve25519_amd64_64_MU2
.globl crypto_scalarmult_curve25519_amd64_64_MU3
.globl crypto_scalarmult_curve25519_amd64_64_MU4
.globl crypto_scalarmult_curve25519_amd64_64_ORDER0
.globl crypto_scalarmult_curve25519_amd64_64_ORDER1
.globl crypto_scalarmult_curve25519_amd64_64_ORDER2
.globl crypto_scalarmult_curve25519_amd64_64_ORDER3
.globl crypto_scalarmult_curve25519_amd64_64_EC2D0
.globl crypto_scalarmult_curve25519_amd64_64_EC2D1
.globl crypto_scalarmult_curve25519_amd64_64_EC2D2
.globl crypto_scalarmult_curve25519_amd64_64_EC2D3
.globl crypto_scalarmult_curve25519_amd64_64_38

.p2align 4

crypto_scalarmult_curve25519_amd64_64_121666:     .quad 121666

crypto_scalarmult_curve25519_amd64_64_MU0:         .quad 0xED9CE5A30A2C131B
crypto_scalarmult_curve25519_amd64_64_MU1:         .quad 0x2106215D086329A7
crypto_scalarmult_curve25519_amd64_64_MU2:         .quad 0xFFFFFFFFFFFFFFEB
crypto_scalarmult_curve25519_amd64_64_MU3:         .quad 0xFFFFFFFFFFFFFFFF
crypto_scalarmult_curve25519_amd64_64_MU4:         .quad 0x000000000000000F

crypto_scalarmult_curve25519_amd64_64_ORDER0:      .quad 0x5812631A5CF5D3ED
crypto_scalarmult_curve25519_amd64_64_ORDER1:      .quad 0x14DEF9DEA2F79CD6
crypto_scalarmult_curve25519_amd64_64_ORDER2:      .quad 0x0000000000000000
crypto_scalarmult_curve25519_amd64_64_ORDER3:      .quad 0x1000000000000000

crypto_scalarmult_curve25519_amd64_64_EC2D0:       .quad 0xEBD69B9426B2F146
crypto_scalarmult_curve25519_amd64_64_EC2D1:       .quad 0x00E0149A8283B156
crypto_scalarmult_curve25519_amd64_64_EC2D2:       .quad 0x198E80F2EEF3D130
crypto_scalarmult_curve25519_amd64_64_EC2D3:       .quad 0xA406D9DC56DFFCE7

crypto_scalarmult_curve25519_amd64_64_38:         .quad 38
