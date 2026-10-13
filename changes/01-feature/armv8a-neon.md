- The ARMv8-A back-end gains the vector registers `v0` to `v31` and the
  Advanced SIMD (NEON) instructions, available as intrinsics on `u128` and
  `u64` values, suffixed with the vector size (`#VAND_128`, `#VAND_64`) or
  with the lane arrangement (`#VADD_4u32`, `#VADD_8u8`): bitwise operations
  (`#VAND`, `#VBIC`, `#VORR`, `#VORN`, `#VEOR`, `#VNOT`, `#VBSL`, `#VBIT`,
  `#VBIF`), lane-wise arithmetic (`#VADD`, `#VSUB`, `#VMUL`, `#VNEG`,
  `#VABS`, `#VSMAX`, `#VSMIN`, `#VUMAX`, `#VUMIN`, `#VMLA`, `#VMLS`, the
  saturating `#VSQDMULH`, `#VSQRDMULH`, `#VSQRDMLAH`, `#VSQRDMLSH` and
  their `LANE` forms, `#VMULLANE`, `#VMLALANE`, `#VMLSLANE`), shifts by
  immediate (`#VSHL`, `#VUSHR`, `#VSSHR`, `#VUSRA`, `#VSSRA`, `#VSLI`,
  `#VSRI`) and by register (`#VUSHL`, `#VSSHL`), permutations (`#VEXT`,
  `#VZIP1`, `#VZIP2`, `#VUZP1`, `#VUZP2`, `#VTRN1`, `#VTRN2`, `#VREV16`,
  `#VREV32`, `#VREV64`, `#VTBL`), comparisons (`#VCMEQ`, `#VCMTST`,
  `#VCMGT`, `#VCMGE`, `#VCMHI`, `#VCMHS`), copies between lanes and general
  registers (`#VDUP`, `#VDUPLANE`, `#VINS`, `#VINSLANE`, `#VUMOV`,
  `#VSMOV`), AES (`#VAESE`, `#VAESD`, `#VAESMC`, `#VAESIMC`), polynomial
  multiplication (`#VPMULL`, `#VPMULL2`) and the SHA-3 instructions
  (`#VEOR3`, `#VBCAX`, `#VRAX1`, `#VXAR`). The bitwise operators on `u128`,
  their zero-extended 64-bit forms, the lane-wise `+`, `-` and `*` and the
  lane-wise shifts by a constant are lowered to these instructions.
