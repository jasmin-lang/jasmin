.text
.p2align 5
.globl _crypto_scalarmult_curve25519_amd64_64_fe25519_mul
.globl crypto_scalarmult_curve25519_amd64_64_fe25519_mul
_crypto_scalarmult_curve25519_amd64_64_fe25519_mul:
crypto_scalarmult_curve25519_amd64_64_fe25519_mul:
	pushq	%rbp
	pushq	%rsi
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	%rdx, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	(%rsi), %rbp
	movq	(%rcx), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	8(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	16(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	24(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r14
	adcq	%rdx, %r8
	movq	8(%rsi), %rbp
	movq	(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	8(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r13
	adcq	$0, %rdx
	addq	%r15, %r13
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	16(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r14
	adcq	$0, %rdx
	addq	%r15, %r14
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	24(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r15, %r8
	adcq	%rdx, %r9
	movq	16(%rsi), %rbp
	movq	(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r13
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	8(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r14
	adcq	$0, %rdx
	addq	%r15, %r14
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	16(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r15, %r8
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	24(%rcx), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r15, %r9
	adcq	%rdx, %r10
	movq	24(%rsi), %rsi
	movq	(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r14
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	8(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r15, %r8
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	16(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r15, %r9
	movq	$0, %r15
	adcq	%rdx, %r15
	movq	24(%rcx), %rax
	mulq	%rsi
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r15, %r10
	adcq	%rdx, %r11
	movq	%r8, %rax
	movq	$38, %rcx
	mulq	%rcx
	movq	%rax, %r8
	movq	%r9, %rax
	movq	%rdx, %r9
	movq	$38, %rcx
	mulq	%rcx
	addq	%rax, %r9
	movq	%r10, %rax
	movq	$0, %r10
	adcq	%rdx, %r10
	movq	$38, %rcx
	mulq	%rcx
	addq	%rax, %r10
	movq	%r11, %rax
	movq	$0, %r11
	adcq	%rdx, %r11
	movq	$38, %rcx
	mulq	%rcx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %rbx
	adcq	%r9, %r12
	adcq	%r10, %r13
	adcq	%r11, %r14
	movq	$0, %rcx
	adcq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %r13
	adcq	%rcx, %r14
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	movq	%r12, 8(%rdi)
	movq	%r13, 16(%rdi)
	movq	%r14, 24(%rdi)
	movq	%rbx, (%rdi)
  popq %r15
  popq %r14
  popq %r13
  popq %r12
	popq	%rbx
	popq	%rsi
	popq	%rbp
	ret 
