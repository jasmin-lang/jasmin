- Every function carries a symbol of its own: an exported one is `.global`, a
  function that is not exported gets an object-local symbol, and both come
  with the same directives (`.type <f>, %function`, and `.thumb_func` on
  ARM), so that every function is visible to `nm`, to a disassembler and to
  stack and size tooling. On ELF targets each function, exported or not, is
  closed by `.size <f>, .-<f>`, so that its symbol has the length of its
  body. Mach-O has neither directive, so the output on that system carries
  neither ([PR #1610](https://github.com/jasmin-lang/jasmin/pull/1610)).
