# Left-values

Left-values appear on the left-hand side of [assignments](code#Assignments) and
[calls](code).
A left-value describes the location where a value is stored.

```
<lval> ::=
  | <var>
  | (<wsize>)[<var> + <expr>] // Memory access.
  | (<wsize>)[<var> - <expr>] // Memory access.
  | <var>[<expr>]  // Array access.
  | <var>[<wsize> <expr>]  // Array access.
  | <var>.[<wsize> <expr>]  // Unscaled array access.
  | <var>[<wsize> <expr> : <expr>]  // Subarray.
  | <var>.[<wsize> <expr> : <expr>]  // Unscaled subarray.
  | _ // Ignored value
```

Left-values syntax is a subset of [expression](expressions), except for `_`
which corresponds to an ignored value.

