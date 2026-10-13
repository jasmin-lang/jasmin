- New command-line option `-function-sections`, off by default and for ELF
  targets only: each function is emitted in a section of its own,
  `.text.<name>`, so that a linker invoked with `--gc-sections` can drop the
  functions that are not reached. Calls internal to the unit keep the
  registers a linker veneer may clobber free across the call (`r12` on ARM,
  `x16`/`x17` on ARMv8-A), which the verified compiler enforces; register
  allocation can therefore differ with and without the option. On the ARM
  targets the internal calls are printed against the quoted symbol of the
  callee, which requires GNU as 2.26 or later
  ([PR #1610](https://github.com/jasmin-lang/jasmin/pull/1610)).
