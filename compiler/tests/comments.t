#[comment = "…"] annotations on functions are printed as comment lines in the
assembly, right after the label of the function, one line per line of text and
in order. Values that are not strings are ignored, and so are inline functions,
which have no label. Comments on statements and declarations are ignored.

  $ ../jasminc comments/x86-64/functions.jazz -o x86-64.s
  $ grep -v '\.ident' x86-64.s
  	.att_syntax
  	.text
  	.p2align	5
  	.global	several
  	.global	frameless
  	.global	framed
  	.type	several, %function
  several:
  // two
  // comments
  	movq	%rdi, %rax
  	ret
  	.size	several, .-several
  	.type	frameless, %function
  frameless:
  // export without a stack frame
  	incq	%rdi
  	movq	%rdi, %rax
  	ret
  	.size	frameless, .-frameless
  	.type	framed, %function
  framed:
  // export with a stack frame
  // second line
  	movq	%rsp, %rsi
  	leaq	-8(%rsp), %rsp
  	andq	$-8, %rsp
  	movq	%rdi, (%rsp)
  	shlq	$1, %rdi
  	call	.Lincr$1
  .Lframed$1:
  	addq	(%rsp), %rdi
  	movq	%rdi, %rax
  	movq	%rsi, %rsp
  	ret
  	.size	framed, .-framed
  	.type	incr, %function
  incr:
  // local function
  .Lincr$1:
  	incq	%rdi
  	ret
  	.size	incr, .-incr
  	.section	".note.GNU-stack", "", %progbits
  $ as x86-64.s -o x86-64.o
  $ ../jasminc -intel comments/x86-64/functions.jazz -o x86-64-intel.s
  $ as x86-64-intel.s -o x86-64-intel.o
  $ grep -c 'first statement\|on a declaration\|inline function' x86-64.s
  0
  [1]

Other architectures.

  $ ../jasminc -arch arm-m4 comments/arm-m4/functions.jazz -o arm-m4.s
  warning: support of the ARM M-profile architectures is experimental
  $ grep -v '\.ident' arm-m4.s
  	.thumb
  	.syntax unified
  	.global	frameless
  	.global	framed
  	.thumb_func
  	.type	frameless, %function
  frameless:
  // export without a stack frame
  	push	{lr}
  	ADD 	r0, r0, #1
  	pop 	{pc}
  	.size	frameless, .-frameless
  	.thumb_func
  	.type	framed, %function
  framed:
  // export with a stack frame
  // second line
  	push	{lr}
  	SUB 	r12, sp, #4
  	BIC 	r12, r12, #3
  	MOV 	r2, sp
  	MOV 	sp, r12
  	STR 	r0, [sp]
  	LSL 	r0, r0, #1
  	bl  	.Lincr$1
  .Lframed$1:
  	LDR 	r0, [sp]
  	ADD 	r0, r1, r0
  	MOV 	sp, r2
  	pop 	{pc}
  	.size	framed, .-framed
  	.thumb_func
  	.type	incr, %function
  incr:
  // local function
  .Lincr$1:
  	ADD 	r1, r0, #1
  	bx  	lr
  	.size	incr, .-incr
  	.section	".note.GNU-stack", "", %progbits
  $ ../jasminc -arch armv8a comments/armv8a/functions.jazz -o armv8a.s
  $ grep -v '\.ident' armv8a.s
  	.global	frameless
  	.global	framed
  	.p2align	2
  	.type	frameless, %function
  frameless:
  // export without a stack frame
  	str 	x30, [sp, #-16]!
  	add 	x0, x0, #1
  	ldr 	x30, [sp], #16
  	ret
  	.size	frameless, .-frameless
  	.p2align	2
  	.type	framed, %function
  framed:
  // export with a stack frame
  // second line
  	str 	x30, [sp, #-16]!
  	sub 	x16, sp, #8
  	and 	x16, x16, #18446744073709551600
  	mov 	x7, sp
  	mov 	sp, x16
  	str 	x0, [sp]
  	lsl 	x0, x0, #1
  	bl  	.Lincr$1
  .Lframed$1:
  	ldr 	x0, [sp]
  	add 	x0, x1, x0
  	mov 	sp, x7
  	ldr 	x30, [sp], #16
  	ret
  	.size	framed, .-framed
  	.p2align	2
  	.type	incr, %function
  incr:
  // local function
  .Lincr$1:
  	add 	x1, x0, #1
  	ret
  	.size	incr, .-incr
  	.section	".note.GNU-stack", "", %progbits
  $ ../jasminc -arch riscv comments/risc-v/functions.jazz -o risc-v.s
  warning: support of the RISC-V architecture is experimental
  $ grep -v '\.ident' risc-v.s
  	.global	frameless
  	.global	framed
  	.type	frameless, %function
  frameless:
  // export without a stack frame
  	addi	sp, sp, -4
  	sw  	ra, (sp)
  	addi	x10, x10, 1
  	lw  	ra, (sp)
  	addi	sp, sp, 4
  	ret
  	.size	frameless, .-frameless
  	.type	framed, %function
  framed:
  // export with a stack frame
  // second line
  	addi	sp, sp, -4
  	sw  	ra, (sp)
  	mv  	x13, sp
  	addi	sp, x13, -4
  	andi	sp, sp, -4
  	sw  	x10, (sp)
  	slli	x10, x10, 1
  	call	.Lincr$1
  .Lframed$1:
  	lw  	ra, (sp)
  	add 	x10, x10, ra
  	mv  	sp, x13
  	lw  	ra, (sp)
  	addi	sp, sp, 4
  	ret
  	.size	framed, .-framed
  	.type	incr, %function
  incr:
  // local function
  .Lincr$1:
  	addi	x10, x10, 1
  	ret
  	.size	incr, .-incr
  	.section	".note.GNU-stack", "", %progbits
