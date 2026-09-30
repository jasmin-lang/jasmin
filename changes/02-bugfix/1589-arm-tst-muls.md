- ARM: the carry flag is undefined after `TST`, as it is after the other
  bitwise operations, instead of being cleared: the processor sets it to the
  carry of the shift or of the expansion of the immediate, or leaves it
  unchanged. The instruction `MULS` cannot be conditional: it has no encoding
  in IT blocks
  ([PR #1589](https://github.com/jasmin-lang/jasmin/pull/1589)).
