# Expressions

Expressions compute values. They appear on the right-hand side of assignments,
in conditions, loop bounds, and anywhere a value is needed.

```
<expr> ::= <literal>
         | <var>
         | <array-access>
         | <memory-load>
         | <pack-expr>
         | <cast-expr>
         | <unary-expr>
         | <binary-expr>
         | <ternary-expr>
         | "(" <expr> ")"
```

## Literals

### Boolean literals

```
reg bool b;
b = true;
b = false;
```

The two Boolean literals are `true` and `false`.

### Integer literals

```
reg u64 x;
x = 42;
x = 0xFF;
x = 0b1010;
x = 0o77;
x = 1_000_000;
x = 0xDEAD_BEEF;
```

Integer literals can be written in decimal, hexadecimal (prefix `0x` or `0X`),
binary (prefix `0b` or `0B`), or octal (prefix `0o` or `0O`).
Underscores can be used as digit separators for readability; they are ignored by
the compiler.

```
<integer> ::= <decimal>
            | "0" ("x" | "X") <hex-digits>
            | "0" ("b" | "B") <bin-digits>
            | "0" ("o" | "O") <oct-digits>
```

Digit groups can be separated by underscores: `1_000`, `0xFF_FF`.

### String literals

```
assert("bounds check", i < 10);
```

String literals are enclosed in double quotes (`"..."`) and support standard
escape sequences. They appear in assertions and annotations.

## Variables

```
x
A::B::x
```

```
<var> ::= <ident> ("::" <ident>)*
```

A variable is a simple identifier or a namespace-qualified name using `::`.
See [namespaces](structure.md#namespaces) for details on qualification.

## Array access

For an array `stack u64[10] a;`, the following access forms are available:

### Scaled element access

```
a[i]          /* i-th element of declared type (u64) */
a[:u16 i]     /* i-th element, viewed as array of u16 */
```

The index `i` is in units of the element type. For `a[i]` with a `u64[10]`
array, index 0 is the first 8-byte element, index 1 is the second, etc.

The `:` prefix before the type is required. The form `a[u16 i]` without `:` is
deprecated.

### Unscaled (direct byte) element access

```
a.[i]         /* byte at offset i, read as declared type (u64) */
a.[:u16 i]    /* byte at offset i, read as u16 */
```

The `.` before the bracket switches to unscaled mode: the index `i` is a
byte offset into the array. For example, `a.[1]` on a `u64[10]` array reads
8 bytes starting at byte offset 1.

### Subarray access

```
a[i:N]        /* N elements starting at index i */
a[:u16 i:N]   /* N u16 elements starting at index i */
a.[i:N]       /* N elements starting at byte offset i */
a.[:u16 i:N]  /* N u16 elements starting at byte offset i */
```

Subarrays extract a contiguous slice of the array. The length `N` must be
a compile-time constant. Subarrays can appear both in expressions and as
[left-values](lvalues.md).

### Alignment annotations

```
a[#aligned i:N]
a[#unaligned i:N]
```

Subarray accesses can be annotated with `#aligned` or `#unaligned` to indicate
alignment properties for vector loads/stores.

### Summary

```
<array-access> ::= <var> <arr-bracket>
                 | <var> "." <arr-bracket>

<arr-bracket> ::= "[" <alignment>? (":" <word-type>)? <expr> (":" <expr>)? "]"

<alignment> ::= "#aligned" | "#unaligned"
```

The `.` switches from scaled (element) to unscaled (byte) indexing.
The optional `:<word-type>` reinterprets the array element type.
The optional `:<expr>` suffix specifies a subarray length.

Jasmin arrays are fundamentally byte arrays in little-endian order.
See the [semantics of arrays](../semantics/arrays.md) for details.

## Memory access (loads)

```
reg u64 x p;
x = [p + 8];              /* load u64 from address p+8 */
x = [:u16 p + 2 * i];     /* load u16 from address p+2*i */
x = [#aligned p];         /* aligned load */
x = [#unaligned :u128 p]; /* unaligned 128-bit load */
```

```
<memory-load> ::= "[" <alignment>? (":" <word-type>)? <expr> "]"
```

A memory load reads a value from a memory address. The expression inside
brackets computes the address. The offset is always in bytes.

The optional `:<word-type>` specifies the width of the load (default depends on
context). The optional `#aligned` or `#unaligned` annotation indicates alignment
expectations for the load instruction.

## Pack expressions

```
reg u128 v;
v = (4u32)[a, b, c, d];       /* pack four u32 values into a u128 */
v = (16u8)[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
```

```
<pack-expr> ::= "(" <svsize> ")" "[" <expr> ("," <expr>)* "]"
```

A pack expression constructs a vector value from a list of element values.
The `<svsize>` specifies the number of elements, signedness, and element
bit-width (see [SIMD vector sizes](types.md#simd-vector-sizes)).
The number of expressions must match the lane count.

The elements are listed in little-endian order: the first element in the list
occupies the least significant bits of the resulting value.
For example, `(4u64)[a, b, c, d]` places `a` in the lowest 64 bits and `d`
in the highest.

## Casts

```
reg u64 x;
reg u32 y;
x = (64u) y;     /* zero-extend u32 to u64 */
x = (64s) y;     /* sign-extend u32 to u64 */
y = (32u) x;     /* truncate u64 to u32 */

reg u64 z;
inline int n;
n = (int) z;     /* word to unbounded integer */
z = (sint) n;    /* integer to word (signed interpretation) */
z = (uint) n;    /* integer to word (unsigned interpretation) */
```

```
<cast-expr> ::= "(" <cast> ")" <expr>

<cast> ::= <word-size> <sign>     /* word cast: (64u), (32s), etc. */
         | "int"                  /* word to int (unsigned) */
         | "sint"                 /* word to int (signed) */
         | "uint"                 /* word to int (unsigned, explicit) */
```

The `<word-size>` is the numeric part of a word type: `8`, `16`, `32`, `64`,
`128`, or `256`. The `<sign>` is `u` (unsigned/zero-extend) or `s`
(signed/sign-extend).

Casts between word types perform zero-extension, sign-extension, or truncation
depending on the relative sizes. `(int)` and `(uint)` convert a word to an
unbounded integer (unsigned interpretation). `(sint)` converts a word to an
integer using signed interpretation.

## Unary operators

```
reg bool b;
b = !b;           /* boolean/bitwise negation */

reg u64 x;
x = -x;           /* arithmetic negation */
```

```
<unary-expr> ::= <unary-op> <expr>

<unary-op> ::= "!" <castop>?
             | "-" <castop>?
```

| Operator | Description |
|----------|-------------|
| `!`      | Boolean negation (on `bool`) or bitwise complement (on word types). |
| `-`      | Arithmetic negation. |

Both operators accept an optional size/sign annotation (see below).

## Binary operators

```
x = a + b;
x = a >>s 4;     /* arithmetic right shift */
x = a /s b;      /* signed division */
x = a +4u64 b;   /* parallel 4-lane u64 addition */
```

```
<binary-expr> ::= <expr> <binary-op> <expr>

<binary-op> ::= <op> <castop>?
```

### Operator list

**Arithmetic:**

| Operator | Description |
|----------|-------------|
| `+`      | Addition |
| `-`      | Subtraction |
| `*`      | Multiplication |
| `/`      | Unsigned division |
| `%`      | Unsigned modulo |

**Bitwise:**

| Operator | Description |
|----------|-------------|
| `&`      | Bitwise AND |
| `\|`     | Bitwise OR |
| `^`      | Bitwise XOR |

**Shifts and rotations:**

| Operator | Description |
|----------|-------------|
| `<<`     | Left shift |
| `>>`     | Unsigned (logical) right shift |
| `<<r`    | Left rotation |
| `>>r`    | Right rotation |

**Comparison:**

| Operator | Description |
|----------|-------------|
| `==`     | Equality |
| `!=`     | Inequality |
| `<`      | Unsigned less than |
| `>`      | Unsigned greater than |
| `<=`     | Unsigned less than or equal |
| `>=`     | Unsigned greater than or equal |

**Logical:**

| Operator | Description |
|----------|-------------|
| `&&`     | Boolean AND (short-circuiting) |
| `\|\|`   | Boolean OR (short-circuiting) |

### Sign modifiers

Division, modulo, right shift, and comparison operators accept an `s` suffix
to select signed semantics:

| Unsigned | Signed |
|----------|--------|
| `/`      | `/s`   |
| `%`      | `%s`   |
| `>>`     | `>>s`  |
| `<`      | `<s`   |
| `>`      | `>s`   |
| `<=`     | `<=s`  |
| `>=`     | `>=s`  |

### Size and vector annotations

Most operators accept a size annotation as a suffix. This forces the
operation to be performed at a specific width or in parallel over vector lanes:

- `+32u` -- 32-bit unsigned addition
- `+8u16` -- parallel addition of 8 unsigned 16-bit lanes (128-bit vector)
- `>>s` -- signed (arithmetic) right shift at the default width
- `:u32` -- can be attached to `!` and `-` as well: `!:u32 x`

The annotation follows the operator and precedes the right operand. The syntax
for annotations is:

```
<castop> ::= <swsize>         /* e.g., 32u, 64s */
           | <svsize>         /* e.g., 4u64, 8u16 */
           | ":" <word-type>  /* e.g., :u32 */
```

Where `<swsize>` is `<size><sign>` (like `32u`, `64s`) and `<svsize>` is the
SIMD vector notation (like `4u64`).
See [SIMD vector sizes](types.md#simd-vector-sizes).

### Precedence

From highest to lowest precedence:

| Precedence | Operators |
|------------|-----------|
| Highest    | `!`, `-` (unary), casts |
| 1          | `*`, `/`, `%` |
| 2          | `+`, `-` |
| 3          | `<<`, `>>`, `<<r`, `>>r` |
| 4          | `&` |
| 5          | `^` |
| 6          | `\|` |
| 7          | `<`, `>`, `<=`, `>=` |
| 8          | `==`, `!=` |
| 9          | `&&` |
| 10         | `\|\|` |
| Lowest     | `? :` (ternary) |

All binary operators are left-associative. The ternary operator is
right-associative.

## Ternary conditional

```
reg u64 x a b;
x = (a > b) ? a : b;   /* maximum of a and b */
```

```
<ternary-expr> ::= <expr> "?" <expr> ":" <expr>
```

The ternary conditional evaluates the condition (first operand) and returns
the second operand if true, or the third if false.

## Comments

Jasmin supports C-style comments:

```
/* This is a block comment.
   It can span multiple lines. */

// This is a line comment.
```

Block comments can be nested: `/* outer /* inner */ still outer */`.
