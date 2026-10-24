- With `-system macosx`, armv8a programs that use global data now produce
  assembly that Apple's assembler accepts: the `ADRP`/`ADD` pair is printed
  with the Mach-O operators `@PAGE` and `@PAGEOFF` instead of the ELF syntax
  ([PR #1594](https://github.com/jasmin-lang/jasmin/pull/1594);
  fixes [#1593](https://github.com/jasmin-lang/jasmin/issues/1593)).
