- armv8a: `u128` values now live in the SIMD&FP registers `v0` to `v31`,
  passed in `v0` to `v7` and returned in `v0` to `v3` as in AAPCS64, with
  `v8` to `v15` callee-saved; the bitwise operators, element-wise addition
  and subtraction, shifts by a constant and the constant zero on `u128`
  are lowered to Advanced SIMD instructions, and the permutations and
  element moves (EXT, REV32, REV64, TRN1, TRN2, ZIP1, ZIP2, UZP1, UZP2,
  DUP, INS, UMOV) are provided as intrinsics. An export function that
  issues a system call now saves and restores `q8` to `q15`
  ([PR #1643](https://github.com/jasmin-lang/jasmin/pull/1643)).
- armv8a: add the SHA-256, SHA-512 and SHA-3 instructions (SHA256H,
  SHA256H2, SHA256SU0, SHA256SU1, SHA512H, SHA512H2, SHA512SU0, SHA512SU1,
  EOR3, BCAX, RAX1, XAR) as intrinsics; the compiler does not check that
  the target implements these optional features, and the assembler has
  to enable them (for llvm-mc, `-mattr=+sha2,+sha3`)
  ([PR #1643](https://github.com/jasmin-lang/jasmin/pull/1643)).
