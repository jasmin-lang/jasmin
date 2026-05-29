# Types and storage

Every variable in Jasmin has a type and a storage class.
The type determines what values the variable can hold;
the storage class determines where it lives at runtime (register, stack, etc.).

## Types

```
<type> ::= "bool"
         | "int"
         | <word-type>
         | <wint-type>
         | <array-type>
         | <ident>
```

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

```
<word-type> ::= "u8" | "u16" | "u32" | "u64" | "u128" | "u256"
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

```
<wint-type> ::= "ui8" | "ui16" | "ui32" | "ui64" | "ui128" | "ui256"
              | "si8" | "si16" | "si32" | "si64" | "si128" | "si256"
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

### Array types

```
stack u64[10] a;
reg u8[32] key;
stack u32[N] buf;   /* N is a param */
```

An array type is written as a base type followed by a size in brackets:

```
<array-type> ::= (<word-type> | <ident>) "[" <expr> "]"
```

The base type is either a word type or an alias to a word type.
The size must be a compile-time constant expression
(a literal, a `param`, or an expression involving only these).
Arrays are fundamentally contiguous sequences of bytes in memory;
the element type determines the default access granularity.

See the [semantics of arrays](../semantics/arrays.md) for details on
access patterns and type punning.

### Type aliases

A type alias (an ident) can be used anywhere a type is expected:

```
type word = u64;
reg word x;       /* equivalent to: reg u64 x */
```

Such aliases can be defined using `type` declarations
(see [type aliases](structure.md#type-aliases)).
Type aliases are resolved at parse time and do not introduce new types.

## Storage qualifiers

Every variable declaration must specify a storage class:

```
reg u64 x;                /* register */
stack u8[32] buf;         /* array in stack */
inline int i;             /* compile-time constant */
global u64 g;             /* global data */
reg ptr u8[32] ptr;       /* pointer to array (the pointer lives in a register) */
stack ptr u8[32] ptr;     /* pointer to array (the pointer lives in the stack) */
```

```
<storage> ::= "reg" <ptr>?
            | "stack" <ptr>?
            | "inline"
            | "global"

<ptr> ::= <writable>? "ptr"
<writable> ::= "const" | "mut"
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

### `reg ptr` and `stack ptr`

Register and stack variables can hold *pointers* to arrays:

```
reg ptr u64[10] p;           /* pointer to array, default mutability */
reg const ptr u64[10] p;     /* read-only pointer */
reg mut ptr u64[10] p;       /* mutable pointer */
stack ptr u64[10] sp;        /* stack pointer to array */
```

A pointer variable does not hold the array data itself; it holds a reference to
an array that lives elsewhere (typically passed as a function argument).
The `const` qualifier prevents writing through the pointer;
`mut` explicitly marks it as writable (this is also the default when neither
`const` nor `mut` is specified).

:::{important}
The storage modifiers can be seen as hints to the compiler.
They do not carry any semantical meaning,
actually they do not even appear in Jasmin's formal semantics.
In particular, `reg ptr` and `stack ptr` are just arrays
semantically-speaking.
See the [semantics of arrays](../semantics/arrays.md)
for more details on this.
:::
