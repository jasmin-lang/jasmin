- The global data of a compilation unit is emitted in a read-only section of
  its own: `.section .rodata,"a",%progbits` on ELF systems, `__TEXT,__const`
  on macOS. Jasmin globals are constants, so the section is never writable.
  (Until this change the data followed the last function: in the text section
  on ARM, ARMv8-A and RISC-V, in `.data` on x86-64.)
  On ARM (Cortex-M) a global is addressed through `MOVW`/`MOVT` immediates
  (`#:lower16:`/`#:upper16:`) that the verified back-end emits, and a global
  load goes through the computed address: the PC-relative literal form is
  resolved by the assembler only within 4 KB in the same section. The ARM
  `ADR` instruction is removed
  ([PR #1578](https://github.com/jasmin-lang/jasmin/pull/1578)).
