- The type checker rejects a vector shift whose sign prefix conflicts with the
  sign in the vector suffix (for instance `>>s4u32`). The scalar form
  (`>>s32u`) was already rejected
  ([PR #1532](https://github.com/jasmin-lang/jasmin/pull/1532);
  fixes [#1441](https://github.com/jasmin-lang/jasmin/issues/1441)).
