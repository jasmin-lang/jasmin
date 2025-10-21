- Printing before parameter substitution now prints variable declarations close
  to their first use, in the deepest possible scope (they used to be printed at
  the top of the function body).
  ([PR #1301](https://github.com/jasmin-lang/jasmin/pull/1301);
  fixes [#1145](https://github.com/jasmin-lang/jasmin/issues/1145)).
