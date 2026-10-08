- Safety checker: a copy at an unknown slice offset no longer hides
  uninitialized cells, loops are analyzed until the initialization of the
  variables is stable, and unbounded memory ranges are reported. A slice of
  an initialized array at an unknown offset is no longer reported
  uninitialized, nor a pointer offset by a `for` loop counter. The
  `CallTopHeuristic` call policy no longer crashes, and start-up is much
  faster with large global arrays
  ([PR #1625](https://github.com/jasmin-lang/jasmin/pull/1625)).
