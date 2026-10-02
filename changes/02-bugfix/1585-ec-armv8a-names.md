- The EasyCrypt extraction of armv8a programs type-checks: the x86
  instructions of `JWord` (theories `ALU` and `SHIFT`) are exported by
  `JModel_x86` only, so that their names do not clash with the armv8a ones
  ([PR #1585](https://github.com/jasmin-lang/jasmin/pull/1585);
  fixes [#1584](https://github.com/jasmin-lang/jasmin/issues/1584)).
