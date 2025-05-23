# Structure

A Jasmin program is a collection of:

  - requires;
  - parameters;
  - global variables;
  - types aliases;
  - functions.

## Require

```
require <string>
```
```
require <string> ... <string>
```
```
from <ident> require <string> ... <string>
```

Since version 2022.04.0, a program may be split into several files using a
`require` clause. Its simplest form is as follows

    require "path/file.jinc"

Relative paths are resolved relative to the current file.

The required file is treated (mostly) as if its contents were put in
place of the `require` clause.

TODO: More detail about "mostly"

Files can also be searched in named locations, for instance:

    from AES require "aes.jinc"

This clause requires the file `aes.jinc` that is located in a path named `AES`.
There are two ways to give names to paths in the file-system:

  - either on the command-line using the argument `-I AES:actual/path/`;
  - or using the `JASMINPATH` environment variable, as in
  `export JASMINPATH=AES=actual/path/`.

If several paths must be named, the `-I` argument can be used multiple
times, and in the environment variable value,
several `ID=path` pairs can be separated by a colon (`:`).

Both `require` clauses and `from` can take several arguments, as in
```
require "path/file1.jinc" "path/file2.jinc" "path/file3.jinc"
```
and
```
from PATH require "file1.jinc" "file2.jinc" "file3.jinc"
```

## Parameters

```
param <type> <ident> = <expr>;
```

A parameter is a named value. The name can be used within types
(e.g., as the size of an array):
as such, they can be used to provide a limited form of genericity.

Parameters are removed by the compiler right after parsing; in particular,
they do not appear
in the Coq abstract syntax. Therefore, they have no formal semantics.

A parameter is introduced by the `param` keyword, followed by a type, a
name, and the value. For instance:

    param int cROUNDS = 2;

## Types Aliases

Jasmin compiler latest development version (still unreleased) introduced a
new syntax feature for type definition. A type alias can be defined at top
level of a program or a namespace. The aim of this feature is to improve
genericity of Jasmin code. The types aliases are resolved like params,
during parsing.

To define a type alias, we introduced the `type` keyword, which is followed
by a name, and the a type. For example :
```
type reg_size = u64;
```
Defined types can then be used in programs in place of the compiler types.
```
reg reg_size a; //declaring variable a with type reg_size
reg reg_size[10] b; //declaring an array with elements of type reg_size
```

We can note that the feature doesn't allow definitions like :
```
type x = reg u64;
```

We can consider that the storage type (`reg`, `stack`, `inline` ...) is
similar to the declaration keyword `let` in other languages (for instance Rust).
Storage type is thus not a type, and should not be aliased.

## Global variables

A global variable is a named valued. Unlike parameters, said value is not
available at compile-time
(i.e., it cannot be used as part of a type), but it is available at run-time.

Technically, global variables are stored in the code segment and are accessed
to using PC-relative addressing mode.

There is no keyword to introduce a global variable declaration at the top-level,
only its type, name, and value. For instance:

    u128 rotate24pattern = (16u8)[ 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1 ];

In this example, the value is a 128-bit machine-word, described as a vector
of 16 8-bit machine-words.

## Functions

A function is introduced using the `fn` keyword, followed by the function name,
the list of its parameters, its return type (if any), and its body.
The body begins with the declaration of local variables and ends with
a `return` statement.

Here is an example function:

    inline
    fn shift(reg u128 x, inline int count) -> reg u128 {
      reg u128 r;
      r = #VPSLL_4u32(x, count);
      return r;
    }

```
export
fn add(reg u64 x, reg u64 y) -> reg u64 {
  reg u64 r;
  r = x;
  r += y;
  return r;
}
```

Function definitions can be prefixed with either the `inline` or `export`
keywords to denote, respectively, that the function will be inlined by the
compiler or that it will respect a specified calling convention.

Since version 2022.04.0, functions may not be marked
with `inline` or `export`. Such functions are called local functions, and
they will be preserved by the compiler but are not visible from the outside
(i.e., they cannot be called from non-Jasmin code).

Function definitions can also be prefixed by annotations.
Annotations are key-value pairs that customize the behaviour of the compiler,
for instance to store the return address of a function in a register or in the
stack.
For instance,
```
#[returnaddress=stack]
fn copy_to_memory(reg u64 x, reg u64 p) {
    [p + 8] = x;
}
```
is a local function that copies the contents of a register `x` to an address
(stored in a register `p`) with an offset of 8, and takes its return address
from the stack.

TODO: Add link to annotation syntax.
