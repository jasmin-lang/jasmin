# Statements

The body of a function is a sequence of statements (instructions).
Each statement can be preceded by [annotations](../annotations/index.md).

```
<block> ::= "{" <instr>* "}"

<instr> ::= <annotations>? <instr-body>

<instr-body> ::= <var-decl>
               | <assignment>
               | <intrinsic-call>
               | <function-call>
               | <conditional>
               | <for-loop>
               | <while-loop>
               | <assertion>
               | <array-init>
```

## Variable declarations

```
reg u64 x;
stack u8[32] buf;
inline int i;
reg u64 a b c;         /* multiple variables, same type */
reg u32 x = 1;         /* declaration with initialization */
reg u64 a = 2, b = a;  /* sequential initialization */
```

```
<var-decl> ::= <storage> <type> <ident> (","? <ident>)* ";"
             | <storage> <type> <ident> "=" <expr> ("," <ident> "=" <expr>)* ";"
```

Each variable must have a [storage qualifier and type](types.md).

For plain declarations (without initialization), the separating comma between
variable names is optional. For declarations with initialization, commas are
mandatory and all variables must have an initial value.

Initialized variables are declared and assigned in order, so later initializers
can reference earlier variables from the same declaration:

```
reg u32 base = 10, exp = x << base;
```

The initial value can be any expression that evaluates to a single value.

## Assignments

```
x = y + 1;
x += y;
x = y if b;
```

```
<assignment> ::= <lvalues> <assign-op> <expr> ("if" <expr>)? ";"

<lvalues> ::= <lvalue> ("," <lvalue>)*
            | "(" ")"
            | <implicits> ("," <lvalue> ("," <lvalue>)*)?

<implicits> ::= "?" "{" <struct-annot> "}"

<assign-op> ::= "="
              | "+=" | "-=" | "*=" | "/=" | "%="
              | "&=" | "|=" | "^="
              | "<<=" | ">>=" | "<<r=" | ">>r="
```

The basic assignment uses `=`. Compound assignment operators (like `+=`) are
syntactic sugar: `x += y` is equivalent to `x = x + y`.

Compound operators can carry size and sign annotations, just like the
corresponding binary operators: `x +=32u y;`, `x >>=s 4;`.

### Conditional assignments

Appending `if <expr>` makes the assignment conditional:

```
x = y if b;       /* assigns y to x only if b is true */
x += z if cond;
```

### Implicit flag capture

Intrinsics and some operations produce CPU status flags. These can be captured
using the `?{ ... }` syntax on the left-hand side:

```
?{of=of, cf=cf}, x = #ADD_64(x, y);
?{}, x = #SUB_64(x, y);     /* ignore all flags */
?{zf=zf}, x = #XOR_64(x, x);
```

The braces contain named flag bindings: `flag_name = variable`.
Use `?{}` to indicate that flags are produced but all are discarded.

### Multiple return values

Functions and intrinsics can return multiple values:

```
q, r = #DIVMOD(x, y);
a, b, c = swap_and_add(a, b, c);
```

Use `_` to discard unwanted return values (see [left-values](lvalues.md)).

## Intrinsic calls

```
of, cf, x = #ROL_64(y, 4);
x = #VPAND_256(a, b);
#VPBROADCAST_4u64(x);
```

```
<intrinsic-call> ::= <lvalues>? "#" <ident> "(" (<expr> ("," <expr>)*)? ")" ";"
```

Intrinsics invoke architecture-specific instructions directly. The instruction
name is prefixed with `#`.

The list of available intrinsics depends on the target architecture and can be
viewed with:

```
jasminc -help-intrinsics
```

### Flag handling

Many intrinsics produce CPU flags as additional outputs. These appear as extra
left-values before the primary result:

```
/* x86-64: ROL produces overflow and carry flags */
of, cf, x = #ROL_64(y, 4);

/* Capture specific flags by name */
?{zf = zero_flag}, x = #AND_64(x, mask);

/* Ignore unwanted flags with _ */
_, _, x = #ADDC_64(x, y, cf);
```

### Architecture examples

**x86-64:**
```
x = #VMOVDQU_256([ptr]);             /* 256-bit unaligned load */
a = #VPSHUFB_256(a, pattern);         /* byte shuffle */
?{cf = cf}, x = #ADD_64(x, y);       /* addition with carry flag */
```

**ARMv7-M (ARM Cortex-M4):**
```
x = #UXTB(y);                        /* unsigned extend byte */
x = #REV(y);                         /* byte reverse */
x = #MUL(x, y);                      /* multiply */
```

**RISC-V:**
```
x = #ADD(x, y);
x = #SLL(x, shift);
```

## Function calls

```
z = add_then_shift(x, y, 2);
do_something(x, y);
a, b = swap(a, b);
r = A::helper(x);
```

```
<function-call> ::= <lvalues> "=" <var> "(" (<expr> ("," <expr>)*)? ")" ";"
                  | <var> "(" (<expr> ("," <expr>)*)? ")" ";"
```

Function calls pass arguments by value and return zero or more values.
The left-hand side is a comma-separated list of [left-values](lvalues.md)
matching the function's result types, followed by `=`.

A function with no results can be called without a left-hand side:

```
store_result(ptr, value);
```

A call can be forced to inline at a specific site using the
[`#[inline]` annotation](../annotations/index.md#inline):

```
#[inline] x = f(y);
```

## Conditionals

```
if x != y {
    x += 1;
}

if x < y {
    x += 1;
} else {
    x += 2;
}

if x < y {
    x = 1;
} else if x == y {
    x = 2;
} else {
    x = 3;
}
```

```
<conditional> ::= "if" <expr> <block> ("else" (<block> | <conditional>))?
```

The `else` branch is optional. Conditionals can be chained with `else if`,
which is syntactic sugar for nested conditionals.

## For loops

```
for i = 0 to 5 {
    a[i] = 0;
}

for i = 4 downto 0 {
    process(a[i]);
}
```

```
<for-loop> ::= "for" <ident> "=" <expr> ("to" | "downto") <expr> <block>
```

For loops execute the body a fixed number of times. The loop variable is
implicitly `inline int` and does not need to be declared.

With `to`, the variable starts at the first bound and increases by 1 each
iteration, stopping *before* reaching the second bound (half-open range).
`for i = 0 to 5` runs with `i` = 0, 1, 2, 3, 4.

With `downto`, the variable starts at the first bound and decreases by 1 each
iteration, stopping *before* reaching the second bound.
`for i = 4 downto 0` runs with `i` = 4, 3, 2, 1.

Both bounds must be compile-time constant expressions. For loops are always
fully unrolled by the compiler.

## While loops

Jasmin supports three forms of while loops:

### Pre-condition (while)

```
while (x <= y) {
    y -= 1;
}
```

The condition is evaluated before each iteration. The body executes only if the
condition is true.

### Post-condition (do-while)

```
while {
    y -= 1;
} (x <= y)
```

The body executes first, then the condition is evaluated. The body always
executes at least once.

### Combined (do-while-do)

```
while {
    y -= 1;
} (x <= y) {
    y -= x;
}
```

The first block (before the condition) executes, then the condition is evaluated.
If true, the second block executes and the loop repeats from the first block.

```
<while-loop> ::= "while" <block>? "(" <expr> ")" <block>?
```

At least one block must be present. The loop entry point can be aligned using
the [`#[align]` annotation](../annotations/index.md#align).

## Assertions

```
assert("bounds check", i < 10);
assert("initialized", is_var_init(x));
```

```
<assertion> ::= "assert" "(" <string> "," <assert-expr> ")" ";"

<assert-expr> ::= "is_var_init" "(" <var> ")"
                | "is_arr_init" "(" <expr> "," <expr> "," <expr> ")"
                | "is_mem_init" "(" <expr> "," <expr> ")"
                | <assert-expr> "&&" <assert-expr>
                | <expr>
```

Assertions are erased by the compiler in an early pass. They do not contribute
to the generated assembly. They are meaningful in the
[reference interpreter](../../tools/reference_interpreter.md) and the
[safety checker](../../tools/safety_checker.md).

The first argument is a label string identifying the assertion. The second
argument is the assertion expression, which can use these special forms:

| Form | Description |
|------|-------------|
| `is_var_init(x)` | Checks that variable `x` is initialized. |
| `is_arr_init(t, ofs, len)` | Checks that bytes `ofs` to `ofs+len` of array `t` are initialized. |
| `is_mem_init(p, len)` | Checks that addresses `p` to `p+len` are initialized. |

Assertion expressions can be combined with `&&`.

## Array initialization

```
stack u64[10] a;
ArrayInit(a);
```

```
<array-init> ::= "ArrayInit" "(" <var> ")" ";"
```

`ArrayInit` marks a stack array as initialized without writing specific values.
This is used to satisfy initialization checks when the array will be fully
written before being read.
