- The armv8a back-end has the vector registers V0–V31: `u128` values live in
  them, are passed and returned in V0–V7 and V0–V3, and the intrinsics
  `#VMOV_128`, `#VLDR_128` and `#VSTR_128` are available
  ([PR #1660](https://github.com/jasmin-lang/jasmin/pull/1660)).
