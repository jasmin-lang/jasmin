# ARMv8-M

The names `armv7m` and `armv8m` of the `-arch` option both select the
`arm-m4` architecture: ARMv8-M with the Main and DSP extensions, as implemented
by the Cortex-M33, has the instructions of ARMv7-M that Jasmin describes
(`proofs/compiler/arm_instr_decl.v`), with the same encodings. The compiler
produces the same code for the three names; the tests of `arm-m4` are also
assembled for the Cortex-M33.

What the Armv8-M Architecture Reference Manual (Arm DDI 0553B.r) says about
this code:

- The 32-bit encodings of the instructions belong to the Main extension; the
  halfword multiplies (`SMULBB` and its kind, `SMULWB`, `SMULWT`), `SMMUL`,
  `SMMULR` and `UMAAL` also need the DSP extension, which is optional on the
  Cortex-M33.
- Bits [1:0] of the stack pointers are RES0H (B3.8, rule R<sub>XPWM</sub>): as
  on ARMv7-M, the compiler keeps the stack pointer 4-byte aligned.
- Data independent timing is defined by the DIT extension, which exists from
  Armv8.1-M (B3.34). On Armv8.0-M processors, such as the Cortex-M33, the
  architecture gives no such guarantee: the classification used by
  `jasmin-ct --doit` is the one of `arm-m4`.
