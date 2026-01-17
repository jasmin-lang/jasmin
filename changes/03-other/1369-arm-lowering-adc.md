- On arm-m4, the add-with-carry operation `_, r = a + b + c` is translated into
  `ADC` (as opposed to `ADCS`) when the output carry is explicitly ignored
  (i.e., written as an underscore)
  ([PR #1369](https://github.com/jasmin-lang/jasmin/pull/1369)).
