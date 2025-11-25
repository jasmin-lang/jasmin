- The deprecated syntax for memory accesses (e.g., `(u8)[p + i]`) is no longer
  supported; the typing annotation should be put *inside* the square brackets
  (i.e., `[:u8 p + i]`) instead
  ([PR #1336](https://github.com/jasmin-lang/jasmin/pull/1336)).
