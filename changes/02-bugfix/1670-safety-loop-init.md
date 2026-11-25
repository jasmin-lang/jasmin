- The safety checker no longer stops analysing a loop while the
  initialization of a variable is still changing, which could miss reads of
  undefined values
  ([PR #1670](https://github.com/jasmin-lang/jasmin/pull/1670)).
