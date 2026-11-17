# ARMv8.1-M

The target architecture `armv8.1m`, also named `cortex-m55` and `cortex-m85`,
is ARMv8.1-M with the Main and DSP extensions, as implemented by the
Cortex-M55 and Cortex-M85 processors. Its reference is the *Armv8-M
Architecture Reference Manual*, Arm DDI 0553B.z; rules are cited by their
identifier, instructions by the number of their section in chapter C2.4.

## One Arm M-profile back-end, several cores

ARMv8.1-M has every instruction of the ARMv7-M model
(`proofs/compiler/arm_instr_decl.v`), with the same encodings, and others. The
`armv8.1m`, `cortex-m4` and `cortex-m3` targets are therefore one back-end,
parameterized by a core (`arm_core` in `arm_decl.v`); the version of the
architecture is one of its fields:

```coq
Variant arm_version := ARMv7M | ARMv8_1M.
```

The instruction descriptions, the compilation passes and their correctness
proofs are generic in the core; what depends on the version is:

- the instructions that exist: the conditional selects below are valid on
  ARMv8.1-M only, and `jasminc -arch cortex-m4` rejects them;
- the instructions that have data independent timing;
- the lowering of conditional assignments.

## Conditional selects

`CSEL`, `CSINC`, `CSINV` and `CSNEG` (C2.4.45, C2.4.48, C2.4.49, C2.4.50)
write to the destination the first source register when the condition
holds, and otherwise the second one, respectively unchanged, incremented,
inverted and negated. They are not permitted in IT blocks and do not set the
flags; the assembly printer prints the condition as their last operand,
without an IT instruction. In the manual, register 15 as a source denotes
the zero register; the model does not describe this form.

On ARMv8.1-M, the lowering pass compiles a conditional assignment between
registers, `x = y if c` or `x = c ? y : z`, to `CSEL`. A conditional
assignment of an expression, `x = y + z if c`, is still compiled to a
conditional instruction, as on ARMv7-M.

## Data independent timing

ARMv8.1-M defines data independent timing in the DIT extension (B3.34).
When `AIRCR.DIT` is 1, the execution time of the instructions whose
description has a "Data Independent Timing behavior" paragraph does not
depend on the values of their operands (R<sub>NXXV</sub>). The
classification used by `jasmin-ct --doit` follows these paragraphs; it is
written in the instruction descriptions, next to the one of the Cortex-M4,
which follows the cycle counts of its Technical Reference Manual. The two
agree on every instruction but `MVN` and the conditional instructions (in
an `IT` block).

- `MVN` does not have data independent timing: its descriptions (C2.4.128,
  C2.4.129) have no such paragraph, although the ones of `ORN` have. To
  negate a secret value in constant time, use `EOR` with the constant `-1`
  instead.
- Conditional instructions do not have it: "DIT behavior only applies if
  the instruction passes its Condition code check" (R<sub>DNPM</sub>), so
  the execution time of a conditional instruction depends on its condition.
  To select on a secret condition, use the conditional selects, which have
  it.
- The loads and the stores have it with respect to the value that is loaded
  or stored, not to the address: "the timing invariance does not apply to
  the addresses being accessed".
- The forms of `ADD` and `SUB` that read `SP` (C2.4.3, C2.4.4, C2.4.237,
  C2.4.238) have no such paragraph, but they are classified with the other
  forms of `ADD` and `SUB`: their operands, the stack pointer and an offset
  in the stack, make an address, which `jasmin-ct` already requires to be
  public.

## Stack pointer

"Bits [1:0] of the MSP or PSP, in either Security state, are RES0H, so that
all stack pointers are always guaranteed to be word-aligned" (B3.8,
R<sub>XPWM</sub>): as on ARMv7-M, the compiler keeps the stack pointer
4-byte aligned.
