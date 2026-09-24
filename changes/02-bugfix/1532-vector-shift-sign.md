- The pre-typing pass rejects vector shifts with two inconsistent signedness
  annotations (e.g., `>>s 4u32`), as is currently done with the scalar form
  (e.g., `>>s 32u`)
  ([PR #1532](https://github.com/jasmin-lang/jasmin/pull/1532);
  fixes [#1441](https://github.com/jasmin-lang/jasmin/issues/1441)).
