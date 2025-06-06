# Selective Speculative Load Hardening

## Selective Speculative Load Hardening (DRAFT)

Jasmin's Selective Speculative Load Hardening is an optimized version
of [Speculative Load Hardening](https://llvm.org/docs/SpeculativeLoadHardening.html)
mitigation method to protect against [Spectre v1](https://spectreattack.com/spectre.pdf)
transient execution attack.

### Background

### Spectre v1 (Bounds check Bypass) attack [brief]
Modern CPUs performs some optimizations like speculation on certain
program behavior to improve the execution speed. One such speculation
is branch prediction, where the CPU will speculate the branch outcome
based on heuristics and starts pre-computing the instructions within
that branch. When the branch condition is resolved, CPU will compare
with its speculation. If the speculation is correct, it will commit
the pre-computation results. Else, it will discard. Though these
speculation does not violate the program semantics, it modifies the
micro-architectural state. The attacker can train and influence the
branch predictor and observe these information leak and obtain secret
information.

Spectre v1 vulnerable *pseudocode* example:
```
if (idx < arrlen) {
    // can enter true branch speculatively
    // even when idx >= arrlen
    idx2 = arr[idx];        // speculative out of bound access
    val = arr2[idx2];       // speculative information leak
}
```
### Speculative Load Hardening (SLH) [simplified]
[SLH](https://llvm.org/docs/SpeculativeLoadHardening.html#high-level-mitigation-approach)
mitigates the Spectre v1 attack by masking the loads(like 0xFFFFFF)
when the CPU is misspeculating with the help of branchless code check.

SLH protection for the above *pseudocode* example:
```
zeros = 0x00000000;
mask = 0xFFFFFFFF;
predicate = zeros;

if (idx < arrLen) {
    // assuming that ternary operator will lower to
    // branchless CMOVxx instruction
    predicate = (idx < arrLen) ? predicate : mask;
    idx2 = arr[idx];
    idx2 = idx2 | predicate;    // mask if misspeculating
    val = arr2[idx2];           // no speculative information leak
}
```
### Constant-Time Programming
A program is said to be a Constant-Time program if it follows below
rules.

1. Secrets do no influence the branch condition.
2. Memory access's index is not influenced by secret.
3. Secrets should not influence the execution time of Time-Variable
   instructions.

### Selective Speculative Load Hardening (in Jasmin)

### SLH v/s Selective SLH

SLH tries to protect all the loads in a given program. This is typical
in an environment when the compiler doesn't know the security level of
a variable. However, cryptographic primitives are written in a
constant-time paradigm and the security levels of the variables are
known. Here, the secrets can only leak speculatively through loading a
public variable. So, we just need to protect public loads only. Hence
the term Selective SLH.

With two-level security annotation and a robust typing rules, Jasmin
can efficiently protect a program using Selective Speculative Load
Hardening against Spectre v1 attacks.

### Misspeculation flag (MSF) states
Misspeculation flag can be in the following three states.
1. `Unknown`: At this state at the given program point, we have no idea
   about speculation status.
2. `Exact`: At this state at the given program point, we know if we are
   misspeculating or not.
3. `Conditioned on b`: At this state at the given program
   point, we have entered a branch where the condtion is bool `b`.
   With the help of `b` we can update our state to `Exact`. If the MSF
   state is not updated correctly before exiting the branch, we will
   transition into `Unknown` state.

### Jasmin primitives to perform SLH
Jasmin provides three main primitives to implement SLH and an extra
primitive to optimize code by moving misspeculation flag.

1. Initializing misspeculation flag:

    `init_msf` calls the memory barrier to stop the exisitng (if any)
    speculation to resolve all the loads at this program execution
    point and initializes the misspeculation flag. MSF will move to
    "Exact" state.
    ```
    #msf reg u64 msf;
    msf = #init_msf();  // Lowered to "lfence; msf = 0"
                        // at this point msf is in Exact state
    ```
2. Updating the misspeculation flag:

    `update_msf` is used to update the misspeculation flag using the
    branch condition and branchless CMOVxx instruction. This will move
    the msf from "Conditioned on b" to "Exact" state.

    ```
    reg bool b;
    #msf reg u64 msf;
    b = i < 10;

    msf = #init_msf();                  // msf in "Exact" state
    if (b) {
                                        // msf in "Conditioned on b" state
        msf = #update_msf(b, msf);      // "msf = b ? msf : -1;"
                                        // msf in "Exact" state
    } else {
                                        // msf in "Conditioned on !b" state
        msf = #update_msf(!b, msf);     // "msf = !b ? msf : -1;"
                                        // msf in "Exact" state
    }
    // msf will be in "Exact" state if and only if
    // in both branches, corresponding msf's state were "Exact"
    // else, it will move to "Unknown" state
    ```
3. Protecting a variable:

    `protect` primitive is used to mask the value using boolean OR if
    it is misspeculating. If not misspeculating, the msf will be 0.
    else, it will be -1. There are other variants like `protect_8`,
    `protect_16`, `protect_32` etc.. to protect different sizes of
    register variable.
    ```
    x = #protect(x, msf);       // Lowered to "x = x | msf;"
    ```
4. Moving misspeculation flag:

    `mov_msf` is used to move a msf from one register variable to
    another register variable. It is often used when there is a
    register pressure and we move it to MMX register variable.
    [TODO: check this properly]
    ```
    #msf regx u64 msfx;
    ....
    msfx = #mov_msf(msf);
    ```
### Annotations supported to perform selective SLH
- `#public` tells the Compiler that this is a public variable.
- `#transient` tells the Compiler that this is a transient variable.
  i.e it is a public variable in normal execution and might contain
  secret speculatively.
- `#secret` tells the Compiler that this is a secret variable.
- `#declassify` tells the compiler that this variable needs to be
  declassified from secret. Compiler changes the type of this variable
  to transient. It can only be made public after `protect`ing it.
- `#msf` tells the Compiler that this is a MSF variable.
- `#inline` tells the Compiler that this expression/block will be
  inlined. Often used in a case when the if's branch condition will be
  resolved statically at compile time and will not be subject to branch
  speculation.
- `#nomodmsf` tells the compiler that this corresponding function will
  not modify the MSF state.

### Things to consider
- MSF variable must be in a register.
- The arguments in the `export` function will be atleast `transient`
  because the `jasminc` compiler does not take MSF variable as an
  argument in `export` function and defensively assumes that we might
  already be misspeculating before executing jasmin `export`
  function.
- In `jasmin` language, `if`, `while`, `init_msf`, `update_msf` and
  calling a system call like `randombytes` will modify the MSF state.
  Hence, cannot be used in a `nomodmsf` function.
- `inline` expression must be resolved at compile time.
- By default, reading data through memory access operation will return
  a `secret` type value.  [TODO: check this.]
- In Jasmin, `for` loop is unrolled and is not subject to branch
  speculation. However, `if` and `while` are subject to branch
  speculation.

### Examples
Let us consider a small example function `encrypt` which takes a msg
and a secret key. It encrypts it using basic XOR operations and then
the final output can be declassifed and make it public.

Unprotected `encrypt` jasmin function example:
```
fn encrypt(reg u64[4] key, reg u64[4] msg) -> reg u64[4] {
    reg u64 i, temp;
    reg u64[4] res;
    reg bool b;

    while {b = i < 4;} (b) {
        temp = msg[(int)i];
        temp = temp ^ key[(int)i];
        res[(int)i] = temp;
        i = i + 1;
    }

    return res;
}
```

Protected `encrypt` jasmin function example:
```
fn encrypt(#secret reg u64[4] key, reg u64[4] msg) -> #public reg u64[4] {
    reg u64 i, temp, msf;
    reg u64[4] res;
    reg bool b;

    msf = #init_msf();
    while {b = i < 4;} (b) {
        msf = #update_msf(b, msf);
        temp = msg[(int)i];
        #declassify temp = temp ^ key[(int)i];
        temp = #protect(temp, msf);             // made public before assigning to res
        res[(int)i] = temp;
        i = i + 1;
    }
    msf = #update_msf(!b, msf);

    return res;
}
```

#### Compiler option
You can use `checkSCT` to check a jasmin file or `checkSCTon` to check
a particular function in a jasmin file.
```
jasminc -checkSCT <filename.jazz>
jasminc -checkSCTon encrypt <filename.jazz>
```

### Additional examples and test cases
For more examples please have a look at success
`compiler/tests/success/slh/x86-64` and failure
`compiler/tests/fail/slh/x86-64` test cases in the source code.
[Libjade](https://github.com/formosa-crypto/libjade) a formally
verified cryptographic library uses this framework to protect its
implementations from Spectre v1 attack.
