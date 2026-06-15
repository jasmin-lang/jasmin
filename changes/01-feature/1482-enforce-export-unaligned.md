- The compiler no longer assumes non-trivial alignment of array arguments to
  export functions; alignment requirements can be expressed through the
  `required_alignment` annotation
  ([PR 1482](https://github.com/jasmin-lang/jasmin/pull/1482)).
