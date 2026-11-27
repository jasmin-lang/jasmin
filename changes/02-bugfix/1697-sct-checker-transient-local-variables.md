- In the SCT checker, local variables are initialized as transient, which partly
  restores a previous behavior. This allows slightly more programs to typecheck
  and/or speculative protections to be removed.

  On the other hand, the `ArrayInit` instruction now initializes the array type
  at transient, as opposed to public, which was a bug.
  ([PR 1697](https://github.com/jasmin-lang/jasmin/pull/1697))
