# Annotations

Annotations attach metadata to functions, parameters, return types, variables,
and statements. They are used to control compiler behavior, declare security
properties, and specify verification contracts.

## Syntax

```
#[returnaddress = stack]
fn f(reg u64 x) -> reg u64 { ... }

#[inline] x = g(y);
```

```
<annotations> ::= <annotation>*

<annotation> ::= "#[" <annot-entry> ("," <annot-entry>)* "]"

<annot-entry> ::= <label> ("=" <attribute>)?

<label> ::= <ident> | <keyword> | <string>

<attribute> ::= <expr>
              | <keyword>
              | <word-type>
              | "{" <struct-annot> "}"

<struct-annot> ::= <annot-entry> ("," <annot-entry>)*
```

Multiple annotations can be written in a single bracket pair separated by commas,
or as separate bracket pairs:

```
#[returnaddress = stack, stacksize = 128]
/* is equivalent to */
#[returnaddress = stack]
#[stacksize = 128]
```

## Function annotations

These annotations appear before a function definition and control
compilation and verification of the function.

### `returnaddress`

```
#[returnaddress = stack]
fn f(reg u64 x) -> reg u64 { ... }
```

Controls where the return address is stored for subroutine (local) functions.

| Value   | Effect |
|---------|--------|
| `stack` | Return address is saved on the stack. |
| `reg`   | Return address is kept in a register. |

Only valid on subroutine functions (not `inline` or `export`).

### `stacksize`

```
#[stacksize = 64]
export fn f(reg u64 x) -> reg u64 { ... }
```

Declares the expected stack frame size (in bytes). The compiler verifies that
the actual stack frame matches this value. Useful for ensuring that code changes
do not inadvertently increase stack usage.

### `stackallocsize`

```
#[stackallocsize = 128]
export fn f(reg u64 x) -> reg u64 { ... }
```

Declares the expected total stack allocation size (frame size rounded up to
alignment, plus extra size). The compiler verifies this after stack allocation.

### `stackalign`

```
#[stackalign = u256]
export fn f(reg u64 x) -> reg u64 { ... }
```

Controls the alignment of the stack frame. The value is a word type indicating
the alignment boundary (e.g., `u256` for 32-byte alignment).

### `calldepth`

```
#[calldepth = 3]
export fn f(reg u64 x) -> reg u64 { ... }
```

Declares the expected maximum call depth for the function. The compiler verifies
this after compilation.

### `stackzero`

```
#[stackzero = loop]
export fn f(reg u64 x) -> reg u64 { ... }
```

Enables stack zeroization: the stack frame is zeroed before the function returns.
Only valid on `export` functions.

| Strategy    | Description |
|-------------|-------------|
| `loop`      | Zero the stack using a loop. |
| `unrolled`  | Zero the stack using unrolled stores. |
| `loopSCT`   | Zero using a loop that preserves speculative constant-time. |

### `stackzerosize`

```
#[stackzero = loop, stackzerosize = u64]
export fn f(reg u64 x) -> reg u64 { ... }
```

Sets the word size used for stack zeroization stores. Must be used together
with `stackzero`. The value is a word type (e.g., `u64`, `u128`).

## Security annotations

These annotations are used by the constant-time and speculative constant-time
checkers to verify information-flow properties.

### `public` / `secret`

```
fn f(#[public] reg u64 x, #[secret] reg u64 y) -> #[public] reg u64 { ... }
```

Placed on function parameters and return types to declare their security level.
The constant-time checker verifies that secret values do not influence
branch conditions or memory access indices.

### `msf`

```
fn f(#[msf] reg u64 ms, #[secret] reg u64 x) -> #[msf] reg u64, reg u64 { ... }
```

Marks a register as carrying the *misspeculation flag* (MSF), used for
Speculative Load Hardening (SLH). An MSF variable tracks whether execution
is on the correct speculative path. It is used by the speculative
constant-time checker.

### `sct`

```
#[sct = "public * secret -> public"]
fn f(reg u64 x, reg u64 y) -> reg u64 { ... }
```

Declares the speculative constant-time type signature of a function as a string.
The signature uses `*` (or `×`) to separate parameter types and `->` (or `→`)
before return types. Each type can be:

- `public` -- publicly observable
- `secret` -- confidential
- `msf` -- misspeculation flag
- `transient` -- public normally, secret speculatively
- `{ normal: <level>, speculative: <level> }` -- explicit per-mode levels
- `{ ptr: <level>, val: <level> }` -- for pointer parameters with separate
  pointer and value levels

### `ct`

```
#[ct = "public * secret -> public"]
fn f(reg u64 x, reg u64 y) -> reg u64 { ... }
```

Declares the (sequential) constant-time type signature. Same string format as
`sct` but without speculative components. Types are `public`, `secret`, or `_`
(unspecified).

## Safety annotations

### `safety`

```
#[safety = {
    args  = { x, y },
    res   = { r },
    requires = x + y <u64 0xFFFFFFFFFFFFFFFF,
    ensures  = r == x + y
}]
fn add(reg u64 x, reg u64 y) -> reg u64 {
    reg u64 r;
    r = x + y;
    return r;
}
```

Declares a safety contract for a function. The annotation is a struct with
the following fields:

| Field      | Description |
|------------|-------------|
| `args`     | Names for the function's input values (used in `requires`/`ensures`). |
| `res`      | Names for the function's output values (used in `ensures`). |
| `requires` | Precondition expression. |
| `ensures`  | Postcondition expression. |

Safety contracts are used by the [safety checker](../../tools/safety_checker.md).

## Variable annotations

These annotations appear on variable declarations.

### `mmx`

```
reg u64 #[mmx] t;
```

Forces the register allocator to place this variable in an MMX register
(x86-64 only).

### `spill_to_mmx`

```
reg u64 #[spill_to_mmx] x;
```

Allows the auto-spiller to use MMX registers for spilling this variable
(x86-64 only).

### `nospill`

```
reg u64 #[nospill] x;
```

Prevents the auto-spiller from spilling this variable.

## Statement annotations

These annotations appear before a statement.

### `inline`

```
#[inline] x = f(y);
```

When placed on a function call statement, forces the called function to be
inlined at this specific call site, regardless of the function's own
calling convention.

### `align`

```
#[align] while { ... } (cond) { ... }
```

When placed on a `while` loop, aligns the loop entry point in the generated
assembly. This can improve performance for tight loops by ensuring the loop
body starts at an aligned address.

## Summary table

| Annotation        | Function | Parameter | Return type | Variable | Statement |
|-------------------|:--------:|:---------:|:-----------:|:--------:|:---------:|
| `returnaddress`   | yes      |           |             |          |           |
| `stacksize`       | yes      |           |             |          |           |
| `stackallocsize`  | yes      |           |             |          |           |
| `stackalign`      | yes      |           |             |          |           |
| `calldepth`       | yes      |           |             |          |           |
| `stackzero`       | yes      |           |             |          |           |
| `stackzerosize`   | yes      |           |             |          |           |
| `public`          |          | yes       | yes         |          |           |
| `secret`          |          | yes       | yes         |          |           |
| `msf`             |          | yes       | yes         |          |           |
| `sct`             | yes      |           |             |          |           |
| `ct`              | yes      |           |             |          |           |
| `safety`          | yes      |           |             |          |           |
| `mmx`             |          |           |             | yes      |           |
| `spill_to_mmx`    |          |           |             | yes      |           |
| `nospill`         |          |           |             | yes      |           |
| `inline`          |          |           |             |          | yes       |
| `align`           |          |           |             |          | yes       |
