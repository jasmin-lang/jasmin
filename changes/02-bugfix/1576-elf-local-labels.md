- Labels internal to a function are now printed with the prefix the target's
  assembler recognises as assembler-local: `.L` on ELF and COFF systems, and
  `L` (unchanged) on macOS. They therefore no longer end up in the symbol
  table of the produced object files on ELF targets
  ([PR #1576](https://github.com/jasmin-lang/jasmin/pull/1576)).
