- With `-system macosx`, armv8a programs that use global data now produce
  assembly that Apple's assembler accepts: the `ADRP`/`ADD` pair is printed
  with the Mach-O operators `@PAGE` and `@PAGEOFF` instead of the ELF syntax.
  The new option `-format elf|mach-o` selects the object format of the
  assembly output (the syntax and the sections); it defaults to `mach-o` with
  `-system macosx` and to `elf` otherwise, and `-system` keeps what belongs to
  the platform, the underscore prefix of the symbols
  ([PR #1594](https://github.com/jasmin-lang/jasmin/pull/1594);
  fixes [#1593](https://github.com/jasmin-lang/jasmin/issues/1593)).
