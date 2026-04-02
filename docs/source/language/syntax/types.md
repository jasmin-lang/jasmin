# Types and storage

Every variable in Jasmin has a type and a storage class.
The type determines what values the variable can hold;
the storage class determines where it lives at runtime (register, stack, etc.).

## Scalar types

### Boolean

```
reg bool b;
b = true;
```

The type `bool` represents Boolean values. Its only values are `true` and `false`.

### Unbounded integers

```
param int N = 10;
inline int i;
```

The type `int` represents mathematical (unbounded) integers.
Variables of type `int` must be known at compile time:
they can only appear with the `inline` or `param` storage.

### Word types

```
reg u64 x;
stack u128 v;
```

Word types represent fixed-width bit vectors:

| Type   | Width   |
|--------|---------|
| `u8`   | 8 bits  |
| `u16`  | 16 bits |
| `u32`  | 32 bits |
| `u64`  | 64 bits |
| `u128` | 128 bits |
| `u256` | 256 bits |

Word types have no inherent signedness. Like in assembly (and unlike C), the
interpretation as signed or unsigned is determined by the operations applied to
them: for example, `>>` is an unsigned (logical) right shift while `>>s` is a
signed (arithmetic) right shift; `<` is an unsigned comparison while `<s` is
signed.

These are the fundamental types that map to machine registers and memory locations.

### Word-sized integers

```
reg ui64 x;
reg si32 y;
```

Word-sized integers are bounded integers that are compiled to machine words.
Unlike word types, arithmetic on word-sized integers follows integer semantics
(e.g., overflow is undefined) rather than modular word semantics.

| Unsigned | Signed | Width |
|----------|--------|-------|
| `ui8`    | `si8`  | 8 bits |
| `ui16`   | `si16` | 16 bits |
| `ui32`   | `si32` | 32 bits |
| `ui64`   | `si64` | 64 bits |
| `ui128`  | `si128` | 128 bits |
| `ui256`  | `si256` | 256 bits |

See the [semantics of scalar types](../semantics/scalar_types.md)
for details on overflow behavior and conversion rules.

### Summary

```
<type> ::= "bool"
         | "int"
         | <word-type>
         | <wint-type>
         | <array-type>
         | <ident>

<word-type> ::= "u8" | "u16" | "u32" | "u64" | "u128" | "u256"

<wint-type> ::= "ui8" | "ui16" | "ui32" | "ui64" | "ui128" | "ui256"
              | "si8" | "si16" | "si32" | "si64" | "si128" | "si256"
```

A `<type>` can also be an `<ident>` referring to a type alias
(see [type aliases](structure.md#type-aliases)).

## Array types

```
stack u64[10] a;
reg u8[32] key;
stack u32[N] buf;   /* N is a param */
```

An array type is written as a base type followed by a size in brackets:

```
<array-type> ::= <type> "[" <expr> "]"
```

The size must be a compile-time constant expression
(a literal, a `param`, or an expression involving only these).
Arrays are fundamentally contiguous sequences of bytes in memory;
the element type determines the default access granularity.

See the [semantics of arrays](../semantics/arrays.md) for details on
access patterns and type punning.

## SIMD vector sizes

Pack expressions and some operator annotations use a *vector size* notation
that specifies the number of lanes, signedness, and element width:

```
(4u64)[a, b, c, d]       /* 4 unsigned 64-bit lanes = 256 bits */
(16u8)[0, 1, 2, ..., 15] /* 16 unsigned 8-bit lanes = 128 bits */
x +4u64 y                /* parallel 4-lane 64-bit addition */
```

The notation is:

```
<svsize> ::= <lane-count> <sign> <element-bits>

<lane-count>   ::= "2" | "4" | "8" | "16" | "32"
<sign>         ::= "u" | "s"
<element-bits> ::= "1" | "2" | "4" | "8" | "16" | "32" | "64" | "128"
```

The total vector width is `<lane-count> * <element-bits>` and must match a
supported word width.
For example, `4u64` describes a 256-bit vector with four unsigned 64-bit elements;
`16s8` describes a 128-bit vector with sixteen signed 8-bit elements.

This notation appears in [pack expressions](expressions.md#pack-expressions)
and as [operator annotations](expressions.md#binary-operators).

## Storage qualifiers

Every variable declaration must specify a storage class:

```
reg u64 x;                /* register */
stack u8[32] buf;         /* stack */
inline int i;             /* compile-time constant */
global u64 g;             /* global data */
```

```
<storage> ::= "reg" <ptr>?
            | "stack" <ptr>?
            | "inline"
            | "global"
```

### `reg`

The variable lives in a machine register. Register variables are the most common
in Jasmin. The register allocator assigns physical registers.

### `stack`

The variable lives on the stack frame. Stack variables are accessed via
stack-relative addressing.

### `inline`

The variable is a compile-time constant. It must be assigned a value that
can be fully evaluated at compile time. Inline variables are erased during
compilation. The loop variable of a `for` loop is implicitly `inline int`.

### `global`

The variable is a read-only global constant. Global variables are compile-time
constants whose values are emitted as bytes in the `.data` section of the
generated assembly. They are accessed via PC-relative addressing and cannot be
modified at runtime.

### Pointer qualifiers

Register and stack variables can hold *pointers* to arrays:

```
reg ptr u64[10] p;           /* pointer to array, default mutability */
reg const ptr u64[10] p;     /* read-only pointer */
reg mut ptr u64[10] p;       /* mutable pointer */
stack ptr u64[10] sp;        /* stack pointer to array */
```

```
<ptr> ::= <writable>? "ptr"
<writable> ::= "const" | "mut"
```

A pointer variable does not hold the array data itself; it holds a reference to
an array that lives elsewhere (typically passed as a function argument).
The `const` qualifier prevents writing through the pointer;
`mut` explicitly marks it as writable (this is also the default when neither
`const` nor `mut` is specified).

## Type aliases

Types can be given alternative names using `type` declarations
(see [type aliases](structure.md#type-aliases)).
A type alias can be used anywhere a type is expected:

```
type word = u64;
reg word x;       /* equivalent to: reg u64 x */
```

Type aliases are resolved at parse time and do not introduce new types.
