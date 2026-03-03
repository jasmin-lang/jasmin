- The semantics of the x86 SIMD shifts (instructions `VPSLL`, `VPSRL`, and
  `VPSRA`) has been corrected: the second operand (the shift amount) is a
  128-bit value, but only its 64 least significant bits are meaningful.
  Consequently, these instructions cannot be used for implementing the Jasmin
  operators such as `<<2u64` in full generality: only selected patterns are
  recognized by the compiler
  ([PR 1399](https://github.com/jasmin-lang/jasmin/pull/1399);
  fixes [#1397](https://github.com/jasmin-lang/jasmin/issues/1397)).
