- armv8a and arm-m4: lower `a & !b` and `!b & a` to BIC, folding a constant
  shift of the complemented operand
  ([PR #1633](https://github.com/jasmin-lang/jasmin/pull/1633)).
