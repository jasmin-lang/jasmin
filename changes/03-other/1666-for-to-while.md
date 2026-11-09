- The extraction to EasyCrypt turns the `for` loops into `while` loops in
  a proved pass (`for_to_while`): a bound read at each iteration that the
  loop may change is copied first into a fresh variable, named after the
  index, and a loop whose index is live after it is guarded so that the
  index holds the last value of its range. In the constant-time models,
  the leakage of a `for` loop is the leakage of the `while` loop it
  becomes: the condition at each iteration, instead of `LeakFor` and the
  bounds; the constructor `LeakFor` is removed from `JLeakage`
  ([PR 1666](https://github.com/jasmin-lang/jasmin/pull/1666)).
