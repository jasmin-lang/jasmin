# Left-values

Left-values (lvalues) describe locations where values can be stored.
They appear on the left-hand side of [assignments](code.md#assignments)
and as outputs of function and intrinsic calls.

```
<lvalue> ::= "_"
           | <var>
           | <var> <arr-bracket>
           | <var> "." <arr-bracket>
           | "[" <alignment>? (":" <word-type>)? <expr> "]"
```

Left-value syntax is a subset of [expression](expressions.md) syntax, with the
addition of `_` (ignored value) which has no expression counterpart.

## Ignored value

```
_, _, x = #ADDC_64(x, y);
_ = f(x);
```

The underscore `_` discards a value. This is commonly used to ignore
flags returned by intrinsics or to discard unwanted return values from
function calls.

## Variable

```
x = 42;
A::x = 0;
```

A simple variable or namespace-qualified name. See [variables](expressions.md#variables).

## Array element and subarray

```
a[i] = x;            /* scaled element store */
a[:u16 i] = y;       /* typed element store */
a.[i] = x;           /* unscaled (byte offset) store */
a.[:u16 i] = y;      /* unscaled typed store */

a[i:N] = f(a[i:N]);  /* subarray store */
a.[i:N] = v;         /* unscaled subarray store */

a[#aligned i:N] = v; /* aligned subarray store */
```

Array left-values use the same syntax as array access in
[expressions](expressions.md#array-access): scaled vs. unscaled (`.`),
optional type annotation (`:u16`), optional subarray length (`:N`),
and optional alignment annotations (`#aligned`, `#unaligned`).

In subarray notation `a[i:N]`, `i` is the starting index (which can be any
expression) and `N` is the *length* (number of elements), not the end index.
The length must be a compile-time constant. For example, `a[2:3]` accesses
3 elements starting at index 2 (i.e., elements 2, 3, and 4).

## Memory store

```
[p + 8] = x;                 /* store u64 at address p+8 */
[:u16 p + 2 * i] = y;        /* store u16 at address p+2*i */
[#aligned p] = v;            /* aligned store */
[#unaligned :u128 p + off] = v; /* unaligned 128-bit store */
```

Memory stores use the same bracket syntax as
[memory loads](expressions.md#memory-access-loads): the expression inside
brackets computes the target address, with optional alignment and type
annotations.
