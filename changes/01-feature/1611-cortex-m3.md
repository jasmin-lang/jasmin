- New target `cortex-m3` for the Cortex-M3 (ARMv7-M): the ARM back-end is
  shared with `cortex-m4` (ARMv7E-M) and rejects the instructions of the DSP
  extension; `jasmin-ct --doit --arch cortex-m3` treats the long
  multiplications (`UMULL`, `SMULL`, `UMLAL`, `SMLAL`, and therefore the wide
  multiplication `hi, lo = x * y`, compiled to `UMULL`) as not DIT
  ([PR #1611](https://github.com/jasmin-lang/jasmin/pull/1611)).
