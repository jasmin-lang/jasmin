# Program structure

A Jasmin source file is a sequence of top-level items:

```
require "common.jinc"

param int N = 10;

type word = u64;

u128 pattern = (16u8)[12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1];

namespace Crypto {
  export fn process(reg u64 p) { ... }
}
```

```
<program> ::= <top-level-item>*

<top-level-item> ::= <require>
                    | <param>
                    | <type-alias>
                    | <global>
                    | <function>
                    | <namespace>
```

## Require

```
require "utils.jinc"
require "file1.jinc" "file2.jinc"
from AES require "aes.jinc"
```

```
<require> ::= "require" <string>+
            | "from" <ident> "require" <string>+
```

A `require` clause includes the contents of another file.
Relative paths are resolved relative to the directory of the current file.
The required file is treated as if its contents were placed at the location
of the `require` clause.

The `from` variant searches for files in a named location. Named locations
can be defined in two ways:

- On the command line: `-I AES:actual/path/`
- Via the environment variable `JASMINPATH`: `export JASMINPATH=AES=actual/path/`

Multiple named paths can be specified by repeating `-I` or separating entries
with `:` in `JASMINPATH`.

Both forms accept multiple file arguments:

```
from PATH require "file1.jinc" "file2.jinc" "file3.jinc"
```

## Parameters

```
param int ROUNDS = 24;
param int BLOCK_SIZE = 4 * ROUNDS;
```

```
<param> ::= "param" <type> <ident> "=" <expr> ";"
```

A parameter is a named compile-time constant. Parameters can be used within
types (e.g., as the size of an array), providing a limited form of genericity.

Parameters are resolved by the compiler right after parsing. They do not appear
in the formal (Coq) abstract syntax and have no formal semantics.

## Type aliases

```
type word = u64;
type block = u32[4];
```

```
<type-alias> ::= "type" <ident> "=" <type> ";"
```

A type alias introduces an alternative name for a type. The alias can then be
used anywhere a type is expected:

```
reg word x;
stack block buf;
```

Type aliases are resolved at parse time, like parameters. They cannot alias
storage qualifiers: `type x = reg u64;` is not valid. See [types](types.md) for
the full set of available types.

## Global variables

```
u128 rotate24pattern = (16u8)[12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5, 0, 3, 2, 1];
u64 constant = 0x1234;
```

```
<global> ::= <type> <ident> "=" <global-expr> ";"

<global-expr> ::= <expr>
                | "{" <expr> ("," <expr>)* "}"
```

A global variable is a named read-only value available at runtime.
Unlike parameters, global values cannot be used as part of a type
(e.g., as an array size), but they can be accessed during execution.

Global variables are stored in the code segment and accessed using PC-relative
addressing. There is no introducing keyword; a top-level declaration without
`param`, `fn`, `type`, or `namespace` is parsed as a global.

The brace syntax allows initializing arrays element by element:

```
u32[4] constants = { 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574 };
```

## Functions

```
inline
fn rotate(reg u32 x, inline int bits) -> reg u32 {
    x = x <<r bits;
    return x;
}

export
fn process(reg u64 ptr) {
    reg u64 t;
    t = [ptr];
    [ptr] = t;
}

#[returnaddress = stack]
fn helper(reg u64 x) -> reg u64 {
    x += 1;
    return x;
}
```

```
<function> ::= <annotations>? <fn-kind>? "fn" <ident>
               "(" <arg-list> ")" ("->" <result-types>)? <body>

<fn-kind> ::= "inline" | "export"

<arg-list> ::= (<annot-arg> ("," <annot-arg>)*)?

<annot-arg> ::= <annotations>? <storage> <type> <ident>+

<result-types> ::= <annot-result> ("," <annot-result>)*

<annot-result> ::= <annotations>? <storage> <type>

<body> ::= "{" <instr>* <return-stmt>? "}"

<return-stmt> ::= "return" <ident> ("," <ident>)* ";"
```

A function is introduced by the `fn` keyword, preceded by an optional
function kind and optional [annotations](../annotations/index.md).

### Kinds of functions

There are three kinds of functions:

**`inline`** -- The function is inlined at every call site. Inline functions
are erased during compilation and produce no standalone assembly code.

**`export`** -- The function is visible from outside (can be called from C or
other non-Jasmin code). It follows the platform ABI for argument passing
and return values.

**No keyword (local/subroutine)** -- The function is compiled as a subroutine
with a Jasmin-internal calling convention. It is not visible to external code
but is preserved as a separate function in the generated assembly.

### Arguments and results

Each argument has an [annotation](../annotations/index.md) (optional),
a [storage qualifier and type](types.md), and one or more names.
Multiple arguments of the same storage and type can share a declaration:

```
fn f(reg u64 x y, stack u8[32] buf) -> reg u64 { ... }
```

Result types are declared after `->` and specify the storage and type
(but not the name) of each result. The names of the returned values
appear in the `return` statement at the end of the function body.

A function with no results omits the `->`:

```
fn store(reg u64 p, reg u64 v) {
    [p] = v;
}
```

### Safety contracts

Functions can be annotated with safety contracts for use with the
[safety checker](../../tools/safety_checker.md):

```
#[safety = {
    args    = { x, y },
    res     = { r },
    requires = x + y <u64 0xFFFFFFFFFFFFFFFF,
    ensures  = r == x + y
}]
fn add(reg u64 x, reg u64 y) -> reg u64 {
    reg u64 r;
    r = x + y;
    return r;
}
```

See the [annotations reference](../annotations/index.md#safety) for details
on the contract fields.

## Namespaces

```
namespace Crypto {
    fn encrypt(reg u64 x) -> reg u64 {
        return x;
    }
}

/* Call from outside: */
r = Crypto::encrypt(x);
```

```
<namespace> ::= "namespace" <ident> "{" <top-level-item>* "}"
```

A namespace groups top-level items under a common prefix.
Items inside a namespace are referenced from outside using `::`:

```
namespace A {
    u32 g = 1;
    fn f(reg u32 x) -> reg u32 { return x; }
}

/* Access: A::g, A::f */
```

Namespaces can be nested:

```
namespace A {
    namespace B {
        fn f(reg u32 x) -> reg u32 { return x; }
    }
}
/* Access: A::B::f */
```

A namespace can be closed and reopened, but items defined in a previous block
of the same namespace must be accessed with the full prefix:

```
namespace A {
    u32 g = 1;
}

namespace A {
    u32 g2 = A::g;  /* A::g must be qualified */
}
```

Export functions inside namespaces have their `::` separators replaced with
`__` in the generated assembly symbol. For example, `A::B::f` becomes
`A__B__f`.
