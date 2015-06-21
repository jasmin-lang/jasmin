# DMASM: Goals

The input language should have a straightforward translation to
assembly code for the given architecture. After expanding all
compile-time constructs, the mapping from DMASM instructions
to assembly instructions should be one-to-one.

We use `x.r` to denote the register assigned to the variable
`x` for the given occurence.

DMASM              X86-64
-----------------  ----------------------------------------------------------
Assignments:
`x = y`            `mov %y.r, %x.r`
`*(x + i) = y`     `mov %y.r, i(%x.r)`
`y = *(x + i)`     `mov i(%x.r), %y.r`
Multiplication:
`(h,l) = x * y`    `mulq %y.r` and `h.r = rdx`, `l.r = x.r = rax`
Addition:
`cf? z += x + cf`  `adc %x.r, %z.r` and `cf` defined
`z += x + cf`      equivalent to previous
`z = z + x + cf`   equivalent to previous
`cf? z += x`       `add %x.r, %z.r`
`z += x`      equivalent to previous
`z = z + x`   equivalent to previous
Subtraction:
`cf? z -= x - cf`  `sbb %x.r, %z.r` and `cf` defined
`z -= x - cf`      equivalent to previous
`z = z - x - cf`   equivalent to previous
`cf? z -= x`       `sub %x.r, %z.r`
`z -= x`           equivalent to previous
`z = z + x`        equivalent to previous



## Notes on X86-64 Instructions

Instruction  References in [1]
-----------  ---------------------
MOV          page 1001
ADC          page 514
ADD          page 519
SBB          page 1442
SUB          page 1490
MULQ         page 1083
IMUL         page 883


### MOV

Memory to memory seems to be allowed.

### ADC/ADD and SBB/SUB

At most one of source/destination can be memory location.

### MULQ

Performs an unsigned multiplication.
In 64 bit mode, source1 is RAX, source2 is either a register or a
memory location, dest is RDX:RAX.

### IMUL

Performs a signed multiplication. There are three different modes:

One operands

: Like MULQ, but with unsigned multiplication. Result in RDX:RAX.

Two operands

: Multiply destination (register) with source (register/memory/immediate)
  and store (truncated) result in destination.

Three operands

: Multiply source1 (register/mem) with source2 (inmediate)
  and store (truncated) result in destination (register).


# References

[1] Intel 64 and IA-32 Architectures Software Developer’s Manual
    Combined Volumes: 1, 2A, 2B, 2C, 3A, 3B and 3C