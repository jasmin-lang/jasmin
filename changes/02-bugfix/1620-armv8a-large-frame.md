- On armv8a, calling a function whose stack frame does not fit in an ADD/SUB
  immediate no longer fails with "instruction SUB_64 is given at least one too
  large immediate as an argument"
  ([PR #1620](https://github.com/jasmin-lang/jasmin/pull/1620)).
