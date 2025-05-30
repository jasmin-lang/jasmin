# Arrays in Jasmin programs

*Caveat: this description applies to Jasmin versions 2022.04.0 and more recent*

## Declaration

Arrays may be allocated in registers, in the stack, or in global memory (i.e., in the code segment, which is immutable).
A declaration of (local) array variables has the following shape:

    stack u64[5] a b c;

 -  storage class (`reg`, `stack`, `reg ptr` or `stack ptr`);
 -  type of the elements;
 -  number of elements, between square brackets;
 -  variable names.

## Access

The common way to access (read or write) an array cell is to use indexing, as in `a[3]` meaning “access the fourth element of array `a`”.

The first element has index zero.

Indexes into register arrays should be statically known
(after inlining, unrolling, and constant propagation).
Otherwise compilation fails.
Indeed, each array cell is allocated to a specific (named) register.

Arrays that are in memory (stack or global) may be indexed by run-time values
(i.e., values that are not statically known).
Such an index may be stored in a register as a machine word:

    reg u64 r i;
    stack u64[4] a;
    …
    r = a[i];

### Explicit scaling

When computing the address of an array element, the index is *implicitly* scaled by the declared sized of the elements in the array.
Consider for instance the following snippet:

    stack u64[4] a;
    a[3] = 1;
    
The second line accesses the 64 bits in memory at offset 3 × 8 after the beginning of the array `a`.
Indeed, according to the declared type of the array, each element is 8 bytes wide, therefore the fourth elements starts at offset 24.
If the index is statically known, scaling is computed at compile-time.

The Jasmin language allows to disable the implicit scaling through the following syntax for direct access (i.e., not scaled):

    a.[24] = 1;
    
Notice the dot before the opening square bracket.

This feature is specially useful when the instruction set does not provide the addressing mode with appropriate scaling.
For instance, on x86-64, scales may only be 1, 2, 4, or 8:
arrays of elements that are 128-bit wide (or more) cannot be accessed using run-time indices that are implicitly scaled.
In the following snippet, the first array access is rejected (“invalid scale”) thus the second form must be used
(with explicit scaling, done as a separate instruction):

    stack u128[2] b;
    reg u64 i;
    reg u128 x;
    …
    x = b[i]; // rejected: invalid scale
    i <<= 4;
    x = b.[i];

### Type punning

Arrays that are in memory are in fact just a plain sequence of contiguous bytes, of some total byte size.
During the lifetime of an array, this byte sequence might be seen in several ways:
as an array of `u8`, or an array of `u16` (if the byte size is even), and so on.
The type chosen at declaration time gives the default view:
an expression `a[i]` means: “access to the *element* at position `i` in array `a`, according to its declared type”.

But on every access, one may use a different view.
For instance, the expression `a[u128 0]` represents an access to the first element of array `a` seen as an array of 128-bit values.

The type written after the left bracket tells the type of the elements of the array for this access.
It is also the type of the value being read or written through said access.

This facility may be used with run-time indices (`a[u16 i]`)
and with explicit scaling (`a.[u128 i]`).

## Intuition about `reg ptr` and `stack ptr`

A `reg ptr` is morally a pointer, and it will be compiled into one. In C, if you declare a pointer (e.g. `int* p;`) and you write to it (e.g. `*p = 4;`) without initializing it, you don't know where you write and you will probably get a runtime error. Likewise, in Jasmin, if you define a `reg ptr` (e.g. `reg ptr u64[2] r;`) and write to it (e.g. `r[i] = 4`) without initializing it (e.g. with `r = t`, where `t` can be a `stack` array, another `reg ptr` or a `stack ptr`), this does not make sense and the compiler will refuse to compile.

There are two cases where `reg ptr` play an important role.
- Accessing a global array: accessing a cell of a global array is not always possible directly. An intermediate `reg ptr` may be needed. Instead of writing `g[i]`, you have to introduce `reg ptr u64[N] r; r = g;` (with the appropriate `N`) and use `r[i]` instead.
- Argument passing: strictly speaking, it is not possible to pass a stack array to a function. What is possible is to pass the address of the array, and this is precisely the role of a `reg ptr`. Instead of calling `f(s)`, you may introduce `reg ptr u64[N] r; r = s;` (with the appropriate `N`) and use `f(r)` instead. You *may*, you do not have to, because there is actually a pass in the compiler that will automatically do this transformation for you, so you can stick to the simple `f(s)` in most scenarios (this pass will introduce a `reg ptr` per call; if this is not what you want, you have to introduce the `reg ptr` manually).

A `stack ptr` is useful only to spill a `reg ptr`, i.e. temporarily store the pointer in the stack. All you can do with a `stack ptr` is copy a `reg ptr` into it or copy it into a `reg ptr`. For instance

```
stack u64[2] s;
reg ptr u64[2] r;
stack ptr u64[2] sp;

r = s;    // r is compiled into a register holding the address of s
sp = r;   // the address is copied in the stack, the register can be used for other purposes
...       // other code not using r
r = sp;   // the address is put back into a register
...       // r can be used again
```
