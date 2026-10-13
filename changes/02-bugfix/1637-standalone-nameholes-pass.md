- Holes (left-values written `_`) are now filled in a standalone pass prior to
  stack-allocation; it also tries to comply with the architectural constraints
  (forced registers, in-place operations) and aborts compilation when this fails
  ([PR 1637](https://github.com/jasmin-lang/jasmin/pull/1637),
  fixes [#679](https://github.com/jasmin-lang/jasmin/issues/679)).
