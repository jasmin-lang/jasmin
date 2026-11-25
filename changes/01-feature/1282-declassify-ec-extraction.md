- `jasmin2ec`: add a new extraction leakage model `-m declassify`, where
  functions additionally return leakage, but only for values explicitly revealed
  with the `#declassify` operator: the full declassified value is leaked,
  nothing else is leaked automatically.
  ([PR #1282](https://github.com/jasmin-lang/jasmin/pull/1282))
