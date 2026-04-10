- Zero-extension from 32/64 to 128 bits on x86 uses the AVX instructions
  (`VMOVD`/`VMOVQ`) instead of the SSE2 instructions (`MOVD`/`MOVQ`)
  ([PR 1433](https://github.com/jasmin-lang/jasmin/pull/1433)).
