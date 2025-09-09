# Scalar types

Jasmin supports 3 families of scalar types (as well as [arrays](arrays) of
scalars): integers, machine words and word-sized integers.

## Integers

Integers are Jasmin values that behave like mathematical integers.
The syntax for this type is `int`.

### Compilation

Values of type `int` must be statically known at compilation.

## Machine words

The machine word types are `u8`, `u16`, `u32`, `u64`, `u128` and `u256`.
These values support the usual (overflowing signed and unsigned) arithmetic, bit-level and logical [operators](../syntax/expressions).

### Compilation

The set of machine words supported is architecture-dependent.

### Verification

The extraction of machine words to EasyCrypt uses the dedicated `W8`, `W16`,
`W32`, `W64`, `W128` and `W256` theories in eclib's `JWord.ec`.

## Word-Sized Integers (aka. wint)

*Caveat: this description applies to Jasmin versions 2025.05.0 and more recent*

Word-sized integers are Jasmin values that behave like (mathematical) integers
(of type `int`) and have statically known bounds so that they can be represented
using machine words. Dually, they are machine words that are always interpreted
as integers, either with the signed interpretation (two’s complement) or with
the unsigned interpretation.

For instance a value declared with type `si8` is an integer in the range [−128;
127] represented as an 8-bit machine word.

The fact these values stay within their given range is the responsibility of the
programmer (and neither the one of the language nor of the compiler): it is
wrong to write programs in which such integers overflow. Yet, this is possible:
do not forget to argue about the safety of Jasmin programs.

The key feature of these data types are for the extraction to EasyCrypt: they
are extracted to `int`, removing the need to deal with modulus 2^XX operations.

### Syntax

The following types describe wint values.
Interpreted in a range of non-negative numbers [0; 2ⁿ−1]: `ui8`, `ui16`, `ui32`, `ui64`, `ui128`, `ui256`.
Interpreted in a range centered on zero [−2ⁿ / 2; 2ⁿ / 2 − 1]: `si8`, `si16`, `si32`, `si64`, `si128`, `si256`.

The following operations are available on wint values.

 - Size-extension / truncation: `(64ui)a`, `(8si)b`
 - Negation: `- b` is the opposite of `b`
 - Addition and subtraction: `+`,  `-`
 - Multiplication, division, remainder: `*`, `/`, `%` (the sign of the result of the remainder operator is the same as the sign of its first operand)
 - Left and right shifts: `<<`, `>>`
 - Comparisons for equality (`==` and `!=`) and ordering (`<`, `<=`, `>`, `>=`)

All operators can be decorated with an optional suffix making explicit the
signedness — for instance `0 <=s b` — or both the size and signedness — for
instance `a + 32ui a`.

### Safety

All operators producing wint values assert, according to Jasmin semantics, that their result is in the expected range.
Execution is stuck if said assertion fails: it is wrong to write programs in which such failures could happen.

### Conversion

Values of wint types can safely be converted to and from machine words using explicit (prefix) conversion operators such as `(32u)` and `(16si)`.

There is no operator to change the signedness of a wint value: it should explicitly be converted to a machine-word and back to a wint.

These values can also be converted to and from (unbounded) `int` values.
Conversion to int is safe and performed through the prefix `(int)` operator or
its more specific variants `(sint)` and `(uint)`. Conversion from `int` is
subject to safety conditions (the value must lie in the target range) and is
performed through a prefix operator such as `(8si)`.

### Compilation

During compilation, wint values are turned into machine words of the
corresponding size and range assertions are dropped.

### Verification

Knowing that wint operations cannot overflow, they can be safely modeled in
EasyCrypt using straightforward operations over integers. Therefore, prior to
extraction to EasyCrypt, wint values are turned into integers.
