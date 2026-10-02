- Various fixes to the EasyCrypt extraction. In particular,
  the extraction of `#randombytes` was changed
  for models `old` and `warray` (no change for model `barray`),
  there is now one version per cell size and per length
  (the case where the cell size is `u8` was not changed
  for backward compatibility).
  ([PR 1563](https://github.com/jasmin-lang/jasmin/pull/1563);
  fixes [#1555](https://github.com/jasmin-lang/jasmin/issues/1555),
  [#1557](https://github.com/jasmin-lang/jasmin/issues/1557)).
