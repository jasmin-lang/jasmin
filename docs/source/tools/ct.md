# Constant-time programming

A program is said to be [constant-time](https://bearssl.org/constanttime.html) when neither the control-flow (in particular conditions of if-then-else blocks and while loops) nor the memory accesses (the memory addresses that are read or written) depend on sensitive data (aka secrets).

## Verification methodology

The adversary power (what can be observed through side-channel attacks) is described through a program instrumentation:
a global variable `leakages` accumulates the data that may leak to the adversary.
The goal is then to prove that when executing the instrumented program, the final value of the `leakages` variable does not contain any sensitive information
Constant-time is a non-interference property; it can be stated as follows: when executing the program twice with the same public inputs (but private inputs may differ), the leaked data is the same.
Initial states that agree on public inputs are often said to be _low-equivalent_.

The EasyCrypt proof assistant is usually powerful enough to automatically prove the constant-time property.
Moreover, it can be used to infer a correct precondition (and hopefully weak), i.e., what inputs must be public for the constant-time property to hold.

In a nutshell, the proof that a Jasmin program is constant-time can be done in the following steps:

0. Ensure that the program is safe
1. Extract to EasyCrypt with explicit leakage
2. State the non-interference property
3. Prove the theorem

## Example

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

    jasmin2ec -f gimli -o gimli_ct.ec gimli.jazz

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
