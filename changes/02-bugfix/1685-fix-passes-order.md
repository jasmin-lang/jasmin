- The pass "lower addressing modes" was wrongly declared to be applied before
  stack allocation. Some tools are not supposed to be called after stack
  allocation but could be called after "lower addressing modes", resulting
  in a crash. The order of the passes was fixed, meaning that these tools
  can no longer be called after "lower addressing modes", avoiding the crash.
  ([PR #1685](https://github.com/jasmin-lang/jasmin/pull/1685)).
