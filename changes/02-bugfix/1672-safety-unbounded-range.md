- The safety checker reports a violation when the memory range of an input
  pointer has an infinite bound, instead of reporting the program safe under a
  precondition that no memory region satisfies
  ([PR #1672](https://github.com/jasmin-lang/jasmin/pull/1672)).
