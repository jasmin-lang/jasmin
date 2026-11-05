- armv8a: new option `-dit` and annotation `#[dit]` to set PSTATE.DIT in
  export functions and restore the caller's value on return; the code then
  requires FEAT_DIT
  ([PR #1678](https://github.com/jasmin-lang/jasmin/pull/1678);
  fixes [#1622](https://github.com/jasmin-lang/jasmin/issues/1622)).
