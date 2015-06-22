# DMASM

The input language should have a straightforward translation to
assembly code for the given architecture. After expanding all
compile-time constructs, the mapping from DMASM instructions
to assembly instructions should be one-to-one.

## DMASM intermediate language: Abstract syntax

The data types for the IL can be found in `IL/IL_Lang.ml`.
There are *compile-time* values and *run-time* values.

### Compile time expressions

* $cvar$: Compile time variables. (Syntax: `n`, `x`, ...)
* $cexp$: Compile time expressions are built from variables,
  integer constants, and $+, *, -$. They are used as indices offset and indices.
  (Syntax: `n + i * 8 - 1`, ...)
* $ccond$: Compile time conditionals are built from compile expressions $e_1, e_2$
  by applying $\bowtie \in \{<,>,\leq,\geq,=,\neq\}$
  and $true, \neg, \land$.
  (Syntax: `n <= 8 && m <> 0`, ...)

### Registers, Sources, and Destinations


A *register* is one of:

* A *machine register* denoted by a string.
  These are fixed and cannot be renamed.
  (Syntax: `%rax`, ...)
* A virtual register denoted by a string and a list
  of compile-time expressions.
  (Syntax: `x[i]`, `x[i,j]`, ...)

To be consistent with assembly terminology, we call
 L-values sources and R-values destinations.

An destination/L-Value is one of:

* A *register*.
* A *memory location* denoted by by a register and
  an offset given as a compile time expression.
  (Syntax: `*(xp + 8)`, `*(%rax + 8)`)

__Note__: the offset is interpreted in bytes and the syntax
is inherited from qhasm. We could enforce that the offset
is divisible by $8$ and work with offsets interpreted as
quad-words (64 bit) internally.

An R/source-Value is one of:

* A *register*.
* A *memory location* denoted by by a register and
  an offset given as a compile time expression.
  (Syntax: `*(xp + 8)`, `*(%rax + 8)`)
* An immediate value.


### Base instructions, If, and For

Base instructions:

* $Move(dest,src)$: Assign value from source to destination.

* $App(op,[dest],[src])$: Apply $op$ to sources and store result
  in destinations.

Instruction:

* $BInstr(bi)$

* $If(ccond,stmt_1,stmt_2)$: If (compile-time) condition $ccond$
  evaluates to $true$, execute $stmt_1$, otherwise, execute $stmt_2$.

* $For(cvar,ce_{from},ce_{to},stmt)$:
    Execute $stmt$ for $cvar$ ranging from $ce_{from}$ to $ce_{to}$.

A statement is a list of instructions.

### Operators and types

$mul : u64 \times u64 \to u64 \times u64$
: unsigned multiplication with full result

$imul : u64 \times u64 \to u64$:
: Truncated signed multiplication.

$add : u64 \times u64 \times bool \to u64 \times bool$
: addition with carry flag (use constant $0/false$ for $ADD$ instruction)

$sub : u64 \times u64 \times bool \to u64 \times bool$
: subtraction with carry flag (use constant $0/false$ for $ADD$ instruction)

shiftleft, bitwise-and, cmov
: to be definedd


## DMASM intermediate language: Type system

Assign types to registers.

We probably need:

* base type: $bool$, $u64$, ...
* array of base type values of size $cexpr$

The type system should ensure memory safety.

## DMASM intermediate language: Semantics

To interpret an IL program, we first require a mapping $\phi$
  from free compile-time variables to integers.

__Note__: the only binder for $cvar$s is $For$.

We also need a mapping $\psi$ from the free registers to values
  of the given types.

__Note__: free registers are either machine registers used for passing
  argument when IL code is called from C or another language
  or virtual registers because we reason about code fragments

## Mapping to X86-64 assembly

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



# Notes on X86-64 Instructions

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