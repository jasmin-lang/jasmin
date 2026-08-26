- On RISC-V, the `DIV`, `DIVU`, `REM` and `REMU` instructions are no longer
  considered constant-time nor DOIT: they have data-dependent latency on
  typical implementations and are excluded from the Zkt ("Data-Independent
  Execution Latency") safe list of the RISC-V specification; every other
  instruction keeps its classification, now documented against the Zkt list
  ([PR 1544](https://github.com/jasmin-lang/jasmin/pull/1544);
  fixes [#1013](https://github.com/jasmin-lang/jasmin/issues/1013)).
