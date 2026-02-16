# Expressions
```
<expr> ::=
  | <int>  // Integer constant.
  | <bool>  // Boolean constant.
  | <var>  // Variable.
  | [<expr>] // Memory access.
  | [:<wsize> <expr>] // Memory access.
  | <var>[<expr>]  // Array access.
  | <var>[:<wsize> <expr>]  // Array access.
  | <var>.[<expr>]  // Unscaled array access.
  | <var>.[:<wsize> <expr>]  // Unscaled array access.
  | <var>[<expr> : <expr>]  // Subarray.
  | <var>[:<wsize> <expr> : <expr>]  // Subarray.
  | <var>.[<expr> : <expr>]  // Unscaled subarray.
  | <var>.[:<wsize> <expr> : <expr>]  // Unscaled subarray.
  | <op1> <expr>  // Unary operation.
  | <expr> <op2> <expr>  // Binary operation.
  | <expr> ? <expr> : <expr>  // Conditional.
  | (<int><sign><int>)[<expr>, ..., <expr>] // Packing.
  | (<expr>)
```

At source level, Jasmin program contain expressions whose concrete syntax is described below.

Expressions are made of:

  - constants (`true`, `false`,  `42`, `0xabcd`);
  - packs (`(4u2)[0, 3, 2, 1]`);
  - variables (`x`);
  - parenthesized subexpressions (`(e)`);
  - memory loads (`[:u16 p + 2 * i]`);
  - array accesses (`x[i]`, `x.[i]`, `x[:u16 i]`);
  - unary operators (`- e`);
  - binary operators (`e - f`);
  - conditional expressions (`c ? th : el`);
  - function calls (`f(x, y)`);
  - primitive instructions (`#copy_32(t)`).

## Unary operators

```
<op1> ::=
  | !        // Boolean and bitwise negation.
  | -        // Arithmetic negation.
  | (<cast>) // Cast.

<cast> ::=
  | <wsize_size><sign>
  | int

```

Unary operators are, by decreasing precedence:

  - zero- or sign-extension (`(16s)e`);
  - boolean / bitwise negation (`! b`);
  - opposite (`- e`).

## Binary operators

```
<op2> ::=
  | +    // Addition.
  | -    // Subtraction.
  | *    // Multiplication.
  | /    // Integer division.
  | %    // Modulo.
  | &    // Bitwise AND.
  | |    // Bitwise OR.
  | ^    // Bitwise XOR (exclusive OR).

  | ==   // Equality test.
  | !=   // Inequality test.
  | <    // Unsgined less than test.
  | <s   // Signed less than test.
  | >    // Unsigned greater than test.
  | >s   // Signed greater than test.
  | <=   // Unsigned less than or equal test.
  | <=s  // Signed less than or equal test.
  | >=   // Unsigned greater than or equal test.
  | >=s  // Signed greater than or equal test.

  | <<   // Left shift.
  | >>   // Right shift.
  | >>s  // Arithmetic right shift.
  | <<r  // Left rotation.
  | >>r  // Right rotation.

  | &&   // Boolean AND.
  | ||   // Boolean OR.
```

- `+`: Addition.
- `<<`: Left shift.
- `>>`: Right shift.
- `>>s`: Arithmetic right shift. In ARM-M4, an arithmetic right shift by 0 is
  compiled to a `MOV`.
- `<<r`: Left rotation.
- `>>r`: Right rotation. In ARM-M4, a right rotation by 0 is compiled to a
  `MOV`.

Binary operators are, by decreasing precedence:

  - multiplication (`x * y`), integer division (`x / y`), and remainder (`x % y`);
  - addition (`x + y`) and subtraction (`x - y`);
  - shifts (`x << y`; `x >>s y`) and rotations (`x <<r y`; `x >>r y`);
  - bitwise and (`x & y`);
  - bitwise exclusive or (`x ^ y`);
  - bitwise or (`x | y`);
  - comparisons (`x < y`; `x >= y`);
  - equality test (`x == y`; `x != y`);
  - boolean conjunction (`b && c`);
  - boolean disjunction (`b || c`).

Note that most operators accept as suffix a size annotation. For instance `+32u` is the 32-bit (unsigned) addition and `+8u16` is the parallel 16-bit (unsigned) addition for vectors of 8 elements (i.e., 128 bit). Said annotation can be limited to a sign annotation, for instance `>>u` is the _logical_ right shift whereas `>>s` is the _arithmetic_ right shift.

## Array access

For an array
```
stack u64[10] x;
```
`x[i]` accesses the i-th element of the array (the first index is 0).

Other indexing syntaxes are available, since Jasmin arrays of any type are
fundamentally byte arrays.
Therefore, accesses with a different type than the declared type of the array
are possible, such as `x[u16 i]` which views `x` as a length 40 array of `u16`
and accesses the i-th element.

Further, non-scaled array accesses are also possible:
`x.[u16 1]` returns the `u16` composed of the second and third bytes of the array.
The explicit type can also be left out `x.[i]` is equivalent to `x.[u64 i]`.

> Note: Jasmin semantics specifies the conversion between bytes and words as little-endian.

## Subarrays

To facilitate array handling, subarray notation was introduced. Consider the
following example,
```
a[i:N] = add_array(a[i:N], b[j:N]);
```
with,
```
inline fn add_array(stack u64[N] a b) -> stack u64[N] {
  inline int i;
  for i = 0 to N {
    reg u64 ai bi;
    ai = a[i];
    bi = b[i];
    ai += bi;
    a[i] = ai;
  }
  return a;
}
```
Subarrays consists on two elements:
- index: where the access starts
- length: amount of elements to access (must be a constant `int`).

Similarly to array indexing, non-scaled subarrays and subarrays with
type-casting are supported: `a.[i:N]`, `a[u16 i:N]`, `a.[u16 i:N]`.

## Memory accesses

Suppose a register `reg u64` whose value is a memory address.
Then, for loading values from memory the notation is as follows:
```
reg u64 var;
var = [ptr + offset];
// or for better understanding
var = (64u)[ptr + offset];
```
`offset` is measured in bytes.

