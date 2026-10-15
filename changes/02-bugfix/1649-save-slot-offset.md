- On arm-m4 and armv8a, the slots of the saved registers of an export function
  are reached directly from SP exactly when their offset is encodable in LDR and
  STR (up to 4095 on arm-m4, a multiple of 8 up to 32760 on armv8a), and
  through a temporary register otherwise. On arm-m4, an offset such as 4096 no
  longer gives an unencodable load or store; on armv8a, the offsets that are
  not ADD immediates no longer go through X17 for nothing.
  ([PR #1649](https://github.com/jasmin-lang/jasmin/pull/1649)).
