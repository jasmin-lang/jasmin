- On armv8a, the stack pointer of export functions is no longer saved in
  `x16`, which made compilation fail with "bad save-stack"
  ([PR #1592](https://github.com/jasmin-lang/jasmin/pull/1592);
  fixes [#1588](https://github.com/jasmin-lang/jasmin/issues/1588)).
