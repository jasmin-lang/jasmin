- The safety checker now keeps the exact bounds of an unsigned right shift by
  a constant, so it can prove the relation between a length and a block count
  derived from it
  ([PR #1650](https://github.com/jasmin-lang/jasmin/pull/1650)).
