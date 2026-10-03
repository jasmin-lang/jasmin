# ARMv8.1-M

The target architecture `armv8.1m` is ARMv8.1-M with the Main and DSP
extensions, as implemented by the Cortex-M55 and Cortex-M85 processors. Its
reference is the *Armv8-M Architecture Reference Manual*, Arm DDI 0553B.r;
rules are cited by their identifier, instructions by the number of their
section in chapter C2.4.

## One Arm M-profile back-end, several cores

ARMv8.1-M has every instruction of the ARMv7-M model
(`proofs/compiler/arm_instr_decl.v`), with the same encodings, and others. The
`armv8.1m`, `arm-m4` and `arm-m3` targets are therefore one back-end,
parameterized by a core (`arm_core` in `arm_decl.v`); the version of the
architecture is one of its fields:

```coq
Variant arm_version := ARMv7M | ARMv8_1M.
```

The instruction descriptions, the compilation passes and their correctness
proofs are generic in the core; what depends on the version is:

- the instructions that exist: the conditional selects below are valid on
  ARMv8.1-M only, and `jasminc -arch arm-m4` rejects them;
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
agree on every instruction but `MVN` and the halfword multiply-accumulates
`SMLA<x><y>`.

- `MVN` has not: its description has no such paragraph (C2.4.128,
  C2.4.129), although the one of `ORN` has, and the 32-bit encodings of
  `MVN` are the ones of `ORN` with register 15 as first operand. On secret
  data, use `EOR` with the constant `-1`.
- `SMLABB`, `SMLABT`, `SMLATB` and `SMLATT` have not: their descriptions
  have no such paragraph, whereas the ones of the halfword multiplications
  `SMUL<x><y>` and `SMULW<y>` have.
- Conditional instructions have not: "DIT behavior only applies if the
  instruction passes its Condition code check" (R<sub>DNPM</sub>), so the
  execution time of a conditional instruction depends on its condition. The
  conditional selects are the instructions to select on a secret condition.
- The conditional selects have data independent timing.
- For the loads and the stores, the execution time is independent of the
  value that is loaded or stored; "the timing invariance does not apply to
  the addresses being accessed".
- The forms of `ADD` and `SUB` that read `SP` (C2.4.3, C2.4.4, C2.4.237,
  C2.4.238) have no such paragraph. The classification is by mnemonic: the
  compiler uses these forms to allocate and free the stack frames, with
  constant sizes.

## Stack pointer

"Bits [1:0] of the MSP or PSP, in either Security state, are RES0H, so that
all stack pointers are always guaranteed to be word-aligned" (B3.8,
R<sub>XPWM</sub>): as on ARMv7-M, the compiler keeps the stack pointer
4-byte aligned.
