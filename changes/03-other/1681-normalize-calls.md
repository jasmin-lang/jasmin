- The extraction to EasyCrypt rewrites, in a proved pass (`normalize_calls`),
  the destinations of calls, system calls and operators with several outputs
  into pairwise distinct variables, copied after the instruction into the
  original destinations; the printer writes these variables directly. In the
  byte-array model, arrays of the same size are interchangeable destinations
  ([PR #1681](https://github.com/jasmin-lang/jasmin/pull/1681)).
