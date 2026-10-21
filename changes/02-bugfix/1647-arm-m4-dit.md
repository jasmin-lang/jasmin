- arm-m4: `RSB`, `REVSH`, `UMAAL`, `SMMUL`, `SMMULR` and the halfword
  multiplications (`SMUL*`, `SMULW*`, `SMLA*`) have data independent timing,
  as every single-cycle instruction of the Cortex-M4 Technical Reference
  Manual; `jasmin-ct --doit --arch arm-m4` accepts secret operands on them.
  Only `SDIV` and `UDIV`, whose cycle count depends on the operands, are not
  ([PR #1647](https://github.com/jasmin-lang/jasmin/pull/1647)).
