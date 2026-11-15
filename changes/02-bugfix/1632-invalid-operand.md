- An argument, destination or condition of an instruction that the target
  cannot express, such as a memory access nested in a larger expression, is
  reported as an error located at the instruction instead of an internal
  error of linearization
  ([PR #1632](https://github.com/jasmin-lang/jasmin/pull/1632);
  fixes [#1126](https://github.com/jasmin-lang/jasmin/issues/1126)).
