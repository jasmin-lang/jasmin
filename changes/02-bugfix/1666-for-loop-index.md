- The EasyCrypt model of a `for` loop leaves its index at the last value of
  the range, and untouched when the range is empty, as the Jasmin semantics
  does; the loops are translated by a proved pass
  ([PR 1666](https://github.com/jasmin-lang/jasmin/pull/1666);
  fixes [issue 1673](https://github.com/jasmin-lang/jasmin/issues/1673)).
