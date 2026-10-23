- ARM: a conditional instruction has data independent timing only when the
  instruction takes one cycle on the Cortex-M4; a conditional load, store,
  `MLA` or `MLS` leaks its condition
  ([PR #1606](https://github.com/jasmin-lang/jasmin/pull/1606)).
