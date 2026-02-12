- Propagation of parameters in array lengths used a wrong implementation
  for unsigned division and unsigned remainder, giving
  possibly wrong results on negative integers
  ([PR 1382](https://github.com/jasmin-lang/jasmin/pull/1382).
