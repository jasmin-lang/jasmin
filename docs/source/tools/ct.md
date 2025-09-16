# Constant-time programming

Constant-time programming is a powerful defense against timing attacks—such as cache attacks—that can completely
compromise otherwise secure systems.
However, writing constant-time code is challenging in itself, and becomes even more difficult when
efficiency or legacy constraints must also be respected.
This makes automated verification of constant-time code a crucial step in the development of secure software,
in particular of cryptographic code.

## Verification methodologies

A program is said to be [constant-time](https://bearssl.org/constanttime.html) when neither the control-flow
(in particular conditions of if-then-else blocks and while loops) nor the memory accesses
(the memory addresses that are read or written) depend on sensitive data (aka secrets).

Jasmin offers two distinct methodologies for verifying that a program executes in constant time.
The first is largely automatic but incomplete; it relies on a type system and can be checked with the `jasmin-ct` tool.
The second requires more user involvement but is more expressive, enabling proofs of the broader notion of probabilistic constant-time.

Both approaches assume that the program is safe, so safety must be established beforehand to ensure that the results of constant-time verification are meaningful.

If you want to be protected against timing attacks based on speculative execution, see section [Selective Speculative Load Hardening](./sct.md)

## Jasmin type system for constant-time

### Command-line interface `jasmin-ct`

To verify that a program is constant-time using Jasmin type system, you can use the `jasmin-ct` tool.

       jasmin-ct [OPTION]… JAZZ

The main options are:

  - `--arch=VAL` (absent=`x86-64`)
    The target architecture (one of `x86-64`, `arm-m4` or `riscv`)
  - `--compile=VAL`, `--after=VAL` (absent=`typing`)
Run after the given compilation pass (one of `typing`, `cstexp`, `wintword`, `arraycopy`, `addarrinit`, `lowerspill`, `inline`, `rmfunc`,
`unroll`, `splitting`, `renaming`, `rmphi`, `renamingd`, `rmarrinit`, `makeref`, `arrexp`, `rmglobals`, `loadconst`, `lowering`, `propagate`, `slhlowering` or `loweraddr`).
The Jasmin compiler should ensure preservation of constant-time. So constant-time can be checked after
any pass, but the type system can be more precise after some step of compilation, in particular after loop unrolling `unroll`.
  - `--doit`
The usual leakage model for constant-time considers that only conditional instructions and load/store
instructions leak. This option allows to consider a stronger model where non Data Independent Timing instructions
leak. In this model, secret data can only be applied to Data Independent Timing instructions ([DOIT](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/data-operand-independent-timing-isa-guidance.html) for Intel and [DIT](https://developer.arm.com/documentation/ddi0595/2020-12/AArch64-Registers/DIT--Data-Independent-Timing) for Arm).
  - `--infer`
Infer security contracts. This can be used for development purpose but should not be used for production.
  - `--print`
Print security type of functions specified by the slice option.
If no slice is provided, print only the type of exported functions.
The option has no effect on the SCT checker.
  - `--print-all`
Print security type of all functions.
The option has no effect on the SCT checker.
  - `--slice=VAL`, `--only=VAL`, `--on=VAL`
Only check the given function (and its dependencies). This argument may be repeated to check many functions.
If not given, all functions will be checked.
  - `--speculative`, `--sct`
Check for speculative constant-time, see section [Selective Speculative Load Hardening](./sct.md).


The full list of options can be obtained using `jasmin-ct --help`.

### Type system

The constant-time type system tracks the security level of each program variable.
A security level can be `public`, `secret`, or a type variable (identifier).
```
  level := secret | public | IDENT
```
`public` is the lowest security level, while `secret` is the highest.
Type variables enable polymorphism in function types.
Intuitively, only `public` data may be allowed to leak.

A type is defined as the maximum of a list of security levels, with the following syntax:
```
  type := level | `{` (level `,`)* level `}`
```

For **expressions**, the type system applies the following rules:

- The type of a constant is `public`.
- The type of an operator is the maximum of the types of its arguments.
  - If `x` has type `public` and `y` has type `secret`, then `x + y` has type `secret`.
  - If `x` has type `l1` and `y` has type `l2`, then `x + y` has type `{l1, l2}`.
- The type of an array read `t[i]` is the type of the array `t`.
  - To be well-typed, the index `i` must be `public`, since `t[i]` compiles to a memory load
and addresses depending on secrets may leak.
- The type of a memory load `[p]` is always `secret`.
  - The accessed address `p`, i.e. the value of the pointer, must be `public`.
- A conditional expression `c ? e1 : e2` does **not** require `c` to be public.
  - It compiles to a conditional move, which is not vulnerable to timing attacks.

For **assignments**, the type system applies the following rules:

- `x = e`: after the assignment, the type of `x` is the type of `e`.
- `t[i] = e`: the index `i` must be `public`.
  - If `t` has type `l1` and `e` has type `l2` before the assignment, then afterwards `t` has type `{l1, l2}`.
- `[p] = e`: requires only that `p` has type `public`.


For conditional instruction (if and while), the type of the condition should be `public`,
`for` loop requires that the bounds have a `public` type.

Each function can be annotated with a security type, the syntax is the following:
```
  level_     := level | `_`
  arg_types  := (level_ (`*`|`×`))* level_
  type_      := type | `_`
  res_types  := (type_ (`*`|`×`))* type_
  fun_type   := (arg_types | `(` arg_types `)`) `->` (res_types | `(` res_types `)`)
```

Function types are specified using `ct` annotation:
```
#[ct = "secret × public -> secret"]
fn add_SP(reg u64 x, reg u64 y) -> reg u64 {
  reg u64 t;
  t = x + y;
  return t;
}
```
The type of `add_SP` specifies that the first argument may have any type up to `secret`,
while the second argument may have at most type `public`.
The return type indicates that the function may produce data dependent on `secret` values
(i.e., the least informative post-condition).

If the type system validates this type, it guarantees that executing the function
will only generate `public` leakage.

When a function takes no arguments (resp. returns no result), the type can be written as `()`.

```
#[ct = "public × secret -> ()"]
fn store(reg u64 p, reg u64 x) {
  [p] = x;
}

#[ct = "() -> public"]
fn zero() -> reg u64 {
  reg u64 z;
  z = 0;
  return z;
}
```

Function types are polymorphic: the type of an argument can be a type variable,
and the return type may depend on it.
```
#[ct = "l1 × l2 -> {l1, l2}"]
fn add(reg u64 x, reg u64 y) -> reg u64 {
  x = x + y;
  return x;
}

#[ct = "secret × public -> secret × secret × secret × public"]
fn add2(reg u64 s, reg u64 p) -> reg u64, reg u64, reg u64, reg u64 {
  reg u64 ss, sp, ps, pp;
  ss = add(s, s);
  sp = add(s, p);
  ps = add(p, s);
  pp = add(p, p);
  return ss, sp, ps, pp;
}
```
The function `add` takes two arguments: the first has type variable `l1`, and the second has type `l2`.
The return type is the maximum of the two, `{l1, l2}`.
Here, `secret` is greater than any other type, and `public` is smaller.

This type is the most general and allows type checking of all four calls in the `add2` function.
In that example, the first three calls return secret data, while the last one returns public data.

The type system does not require annotations for internal (non-exported) functions,
since it can automatically infer their types.
However, you may still annotate internal functions for documentation purposes.
Types can also be partially specified using `_`.
```
#[ct = "_ × public -> _ × public"]
fn set0_incr (reg ptr u64[4] t, reg u64 i) -> reg ptr u64[4], reg u64 {
   t[i] = 0;
   i += 1;
   return i, t;
}
```
In this case, the type system will automatically fill in the `_`.
For `set0_incr`, the inferred type is: `t × public -> t × public`.

If the type provided is not the most general one, the type system keeps the more restricted one:

```
#[ct = "_ × public -> secret"]
fn add_restr(reg u64 x, reg u64 y) -> reg u64 {
  x = x + y;
  return x;
}
```
In this case, the type system infers the type `x × y -> {x, y}`,
but respects the user-defined constraint by keeping a more restrictive type.
It takes the minimal security level of the inputs and the maximum of the output types.
The final type is therefore:  `x × public -> secret`.

For exported functions, providing an explicit type is mandatory.
You can use the `--infer` option to have the type system infer it automatically,
but you should always verify that the inferred type matches your expectations.
**WARNING:** This feature is intended for development purposes only and should **not** be used in production.


### Declassification

The type-system is not complete: some secure programs are not well-typed. One
possible way around this limitation is to use some “declassification”, i.e., to
explicitly mark some data as public although the rules of the type-system would
label them as secret.

The type-checker supports a `declassify` annotation on assignments and labels
the written values as public.

For instance, a value read from memory may be *a priori* known to be public
(although the type-system usually treats memory contents as secret).

~~~
#[ct="public → public"]
fn get_param(reg u64 pointer) -> reg u8 {
  reg u8 value;
  // This declassify is safe because we know (by other means…)
  // that pointer targets public data
  #declassify
  value = [:u8 pointer];
  return value;
}
~~~

An other textbook example of declassification is that the result of encryption, although depending on a secret key and a sensitive message, can be publicly disclosed.

~~~
#[ct="secret → public × secret"]
fn otp(reg u32 msg) -> reg u32, reg u32 {
  stack u32[1] rnd;
  rnd = #randombytes(rnd);
  reg u32 key = rnd[0];
  // This declassification is safe because msg is encrypted with the secret key
  #declassify
  msg ^= key;
  return msg, key;
}
~~~

The type-checker does not attempt to prove that the annotation is valid, i.e.,
that the declassified value is indeed public: indeed, the purpose of the
annotation is to escape the fundamental limitation of the type-system.
Therefore, every declassify annotation must be justified by other means,
depending on the specific case.

### Fine-grained constant-time policies (DOIT)

In addition to the usual constraints that branching conditions and memory
addresses must be public, the type-checker can also enforce that arguments to
*variable-time instructions* are public. To this end, the “doit” mode of the
checker can be enabled using the corresponding `--doit` command-line flag. It
checks that arguments to assembly instructions that are not in the “DOIT” list
are indeed public.

In order to know what assembly instructions are emitted by the compiler, the
checker has to run after instruction selection. More specifically, using the
`--doit` mode makes verification occur after the [“Propagate
Inline”](../compiler/passes/propagate_inline) compilation pass (or any further
pass specified by the `--after` argument).

For instance, the following program is accepted by the type-checker, but rejected in “doit” mode,
as the rotation instructions (on x86_64) are not listed as DOIT.

~~~
#[ct="secret → secret"]
export
fn rotate(reg u32 x) -> reg u32 {
  x = x;
  x >>r= 1;
  return x;
}
~~~

What instructions are considered secure depends on the target architecture.

Third-party references:

- [List of DOIT instructions on Intel platforms](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html)
- [ARM documentation for DIT](https://developer.arm.com/documentation/ddi0601/2025-06/AArch64-Registers/DIT--Data-Independent-Timing)

More details can be found in the following paper:

> Arranz-Olmos, S., Barthe, G., Grégoire, B., Jancar, J., Laporte, V., Oliveira,
T., & Schwabe, P. (2025). Let’s DOIT: Using Intel’s Extended HW/SW Contract for
Secure Compilation of Crypto Code. *IACR Transactions on Cryptographic Hardware
and Embedded Systems*, 2025(3), 644-667.
<https://doi.org/10.46586/tches.v2025.i3.644-667>


### Some examples

The following example is rejected because the `if` instruction depends on the secret data `x`.
```
#[ct = "secret -> secret"]
fn leak_cond(reg u64 x)  -> reg u64 {
  reg u64 y = 0;
  if (x == 0) { y = 1; }
  return y;
}
```

The following example is rejected because the store instruction depends on the secret data `p`.
```
#[ct = "secret -> secret"]
fn leak_store(reg u64 p) {
  [p] = 0;
}
```

In the following example, the array is `public`, meaning that the contents of its cells depend only on public information,
so reading from the array would normally yield a public value.
However, the program is rejected because the array access depends on the secret data `i`.
Note that array accesses are compiled to memory load instructions, which may leak information if the index is secret.
```
#[ct = "public × secret -> public"]
fn leak_arr_load(reg ptr u64[4] t, reg u64 i) -> reg u64 {
  reg u64 x;
  x = t[i];
  return x;
}
```

Data loaded from memory have type secret:
```
#[ct = "public -> secret"]
fn load_mem(reg u64 p) -> reg u64 {
  reg u64 r;
  r = [p];
  return r;
}
```

When the type of a function is specified, any call to the function must respect its type.
```
#[ct = "secret × public -> secret"]
fn add_SP(reg u64 x, reg u64 y) -> reg u64 {
  reg u64 t;
  t = x + y;
  return t;
}

#[ct = "secret -> secret"]
fn bad_call(reg u64 x) -> reg u64 {
  x = add_SP(x, x);
  return x;
}
```
The type system will reject this program because the second argument of `add_SP` is secret while the type of the function
requires it to be public.


## Establishing constant-time using extraction to EasyCrypt

The adversary power (what can be observed through side-channel attacks) is described through a program instrumentation:
a global variable `leakages` accumulates the data that may leak to the adversary.
The goal is then to prove that when executing the instrumented program, the final value of the `leakages` variable does not contain any sensitive information.
Constant-time is a non-interference property; it can be stated as follows: when executing the program twice with the same public inputs (but private inputs may differ), the leaked data is the same.
Initial states that agree on public inputs are often said to be _low-equivalent_.

The EasyCrypt proof assistant is usually powerful enough to automatically prove the constant-time property.
Moreover, it can be used to infer a correct precondition (and hopefully weak), i.e., what inputs must be public for the constant-time property to hold.

In a nutshell, the proof that a Jasmin program is constant-time can be done in the following steps:

0. Ensure that the program is safe
1. Extract to EasyCrypt with explicit leakage
2. State the non-interference property
3. Prove the theorem

### Example

To illustrate the methodology, let’s consider a reference implementation of the Gimli permutation
(to be found in [compiler/examples/gimli/x86-64/gimli.jazz](https://github.com/jasmin-lang/jasmin/blob/master/compiler/examples/gimli/x86-64/gimli.jazz)):

```
export
fn gimli(reg ptr u32[12] state) -> reg ptr u32[12] {
  inline int round, column;
  reg u32 x, y, z;
  reg u32 a, b, c;

  for round = 24 downto 0 {
    for column = 0 to 4 {
      x = state[0 + column];
      x <<r= 24;
      y = state[4 + column];
      y <<r= 9;
      z = state[8 + column];

      a = x;
      b = z; b <<= 1;
      c = y; c &= z; c <<= 2;
      a ^= b; a ^= c;

      state[8 + column] = a;

      a = y;
      b = x; b |= z; b <<= 1;
      a ^= x; a ^= b;

      state[4 + column] = a;

      a = z;
      b = x; b &= y; b <<= 3;
      a ^= y; a ^= b;

      state[0 + column] = a;
    }

    if (round % 4) == 0 { // small swap: pattern s...s...s... etc.
      x = state[0];
      y = state[1];
      state[0] = y;
      state[1] = x;

      x = state[2];
      y = state[3];
      state[2] = y;
      state[3] = x;
    }

    if (round % 4) == 2 { // big swap: pattern ..S...S...S. etc.
      x = state[0];
      y = state[2];
      state[0] = y;
      state[2] = x;

      x = state[1];
      y = state[3];
      state[1] = y;
      state[3] = x;
    }

    if (round % 4) == 0 { // add constant: pattern c...c...c... etc.
      state[0] ^= 0x9e377900 + round;
    }
  }
  return state;
}
```

This program is safe, as long as the `state` argument points to a valid memory region of at least 48 bytes, aligned for 32-bit accesses.
This is automatically proved by the safety checker, called as follows:

    jasminc -checksafety gimli.jazz

The EasyCrypt model for constant-time verification can be obtained by calling `jasmin2ec` as follows:

    jasmin2ec -m CT -f gimli -o gimli_ct.ec gimli.jazz

This produces an EasyCrypt file `gimli_ct.ec` that looks like what follows.

~~~
module M = {
  proc gimli (state:BArray48.t) : JLeakage.leakage * BArray48.t = {
    var leak:JLeakage.leakages;
    var leak_b:JLeakage.leakages;
    var round:int;
    leak <- [];
    leak <- (leak ++ [(LeakList [(Leak_int 24); (Leak_int 0)])]);
    round <- 24;
    (* ... *)
    leak <- (leak ++ [(LeakList leak_b)]);
    return ((LeakList leak), state);
  }
}.
~~~

There is a module `M` with a model of each function, where the functions return a leakage value in addition to the return value corresponding to the Jasmin semantics.
Each operation that may leak some data has been instrumented to accumulate the leakage in that leakage value.

Now the constant-time property of the `gimli` function can be (manually) stated.
In a fresh file, the generated `Gimli_ct` module is first required,
and the property stated using pRHL as follows.

```
require Gimli_ct.

equiv gimli_ct :
  Gimli_ct.M.gimli ~ Gimli_ct.M.gimli :
  true ==> res{1}.`1 = res{2}.`1.
proof. proc; inline *; sim: (={leak}). qed.
```

## SCT-checker annotations

The SCT-checker accepts “sct” annotation for functions. The value of this annotation is a security signature for the function. Said signature gives the security type of each argument and returned value.

A security level is made of two components: one for normal, correctly speculated executions (this component is labelled with “normal” or “n”); the other component for mis-speculated executions (it is labelled with “speculative” or “s”). Each component is one of:

- “public”
- “secret”
- an arbitrary identifier

There are a few notational shortcuts:

- “transient” denotes the level { normal: public, speculative: secret }
- a lone component x denotes the pair { n: x, s: x }

A type for non-ptr variables is just a level or the special name “msf”. A type for a ptr variable is made of two levels: one for the value (i.e., the array), the other one for the reference (aka the pointer) which may become transient when unspilled from memory.

The msf type qualifies values that are public in all executions (i.e., {n: public, s: public}) and correctly reflect the mis-speculation state of the micro-architecture.
