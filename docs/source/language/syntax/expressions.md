# Expressions
```
<expr> ::=
  | <int>  // Integer constant.
  | <bool>  // Boolean constant.
  | <string> // String constant.
  | <var>  // Variable.
  | [<align> <expr>] // Memory access.
  | [<align>:<wsize> <expr>] // Memory access.
  | <var>[<align> <expr>]  // Array access.
  | <var>[<align>:<wsize> <expr>]  // Array access.
  | <var>.[<align> <expr>]  // Unscaled array access.
  | <var>.[<align>:<wsize> <expr>]  // Unscaled array access.
  | <var>[<expr> : <expr>]  // Subarray.
  | <var>[:<wsize> <expr> : <expr>]  // Subarray.
  | <var>.[<expr> : <expr>]  // Unscaled subarray.
  | <var>.[:<wsize> <expr> : <expr>]  // Unscaled subarray.
  | <op1> <expr>  // Unary operation.
  | <expr> <op2> <expr>  // Binary operation.
  | <expr> ? <expr> : <expr>  // Conditional.
  | (<int><sign><int>)[<expr>, ..., <expr>] // Packing.
  | (<expr>)

<align> ::=
  |
  | #aligned
  | #unaligned
```

At source level, Jasmin program contain expressions whose concrete syntax is described below.

Expressions are made of:

  - constants (`true`, `false`,  `42`, `0xabcd`);
  - packs (`(4u2)[0, 3, 2, 1]`);
  - string literals (`"Hello World!"`);
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

Suppose a register variable `reg u64 pointer` whose value is a memory address.
Then, for loading values from memory the notation is as follows:
```
reg u64 var;
var = [pointer + offset];
// or for better understanding
var = [:u64 pointer + offset];
```
`offset` is measured in bytes and may be an expression, depending on the
addressing modes available on the target platform.

## Alignment assumptions

Memory and array accesses may have alignment annotations, either `#aligned` or
`#unaligned`. They denote whether, *after compilation*, the pointer (i.e.,
memory address) underlying the access is aligned, i.e., a multiple of the size
(in bytes) of the accessed data.

When no annotation is given it defaults to `#unaligned`.

They are used in two ways by the compiler:

1. when selecting instructions and generating assembly, to pick appropriate
   instructions and discharge their preconditions regarding alignment (if any);
2. when allocating local variables into the stack, the layout of each frame is
   computed so that these assumptions are met (knowing that each `export`
   function enforces that the stack pointer is sufficiently aligned initially).

Therefore, some of these annotations hold by virtue of the correctness of the
compiler, but the other ones are **assumptions**, used as trusted hints by the
compiler. Notably the ones that involve pointers or arrays that are arguments to
export functions. The [safety checker](../../tools/safety_checker) may prove
that some of them hold, the remaining ones are plain assumptions about the
external world.

In short, `#unaligned` accesses can be used both with aligned and unaligned
pointers and the compiler turns them into instructions that do not have any
alignment requirement; when applied to data that is stored in the local stack of
some Jasmin function, the compiler will nonetheless attempt to layout the stack
frames in such a way that the resulting pointers are aligned. On the other hand,
`#aligned` accesses must be applied to aligned pointer and thus the compiler may
turn them into instructions that require this alignment (e.g., `vmovdqa` on
x86_64).

When some array accesses assume that some `export` functions receive **aligned**
pointers as argument, these requirements **must** be documented. Otherwise the
[stack allocation pass](../../compiler/passes/stack_alloc) will produce an
error. To describe alignment requirements, function declarations can be
decorated with a `required_alignment` annotation whose value is a map whose keys
are *names* of function parameters and values are word-sizes. Parameters of the
function that are not bound in this map have no requirement. For instance, the
program below reads from its `src` parameter assuming it is aligned to 32 bytes.
Alignment makes no sense for the numerical `offset` parameter and is irrelevant
for the `dst` parameter; therefore none of them is listed in the annotation.

~~~
#[required_alignment = { src = u256 }]
export
fn copy_256AU(reg ptr u256[4] dst src, reg u64 offset) -> reg ptr u256[4] {
  offset &= 3;
  offset <<= 5;
  reg u256 t = #VMOVDQA_256(src.[#aligned offset]);
  dst[#unaligned 0] = t;
  return dst;
}
~~~

When used on local functions, this annotation acts as an assertion about the
upper bound on the expected alignment and as a lower bound that the compiler
should enforce. In the following example, the annotation claims that indeed, no
access inside the function needs a more specific alignment than what is written
and asks the compiler to enforce that the arrays that are given as argument are
at least as aligned as what is written.

~~~
#[required_alignment = { dst = u32, src = u128 }]
fn copy(reg ptr u8[4] dst src) -> reg ptr u8[4] {
  reg u32 x = src[#unaligned:u32 0];
  dst[#aligned:u32 0] = x;
  return dst;
}

#[stackalign = u128]
export
fn main(reg ptr u8[4] p) -> reg u32 {
  stack u32[3] data;
  reg ptr u32[1] in = data[0:1], out = data[2:1];
  reg u32 v = p[#unaligned:u32 0];
  in[#unaligned 0] = v;
  out = copy(out, in);
  v = out[#unaligned 0];
  return v;
}
~~~
