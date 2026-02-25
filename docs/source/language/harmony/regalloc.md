# Register allocation
The main difference between the Jasmin compiler and more traditional compilers lies
in **register allocation**. While traditional languages only manipulate variables abstractly,
Jasmin allows the programmer to specify where variables are stored, either in memory (`stack`) or in registers (`reg`).
Moreover, the compiler does not introduce any automatic spilling (saving registers to the stack)
nor any additional register assignments.
This design choice introduces strong constraints during register allocation.

## Constraints Imposed by the architecture

During register allocation, the compiler must map every `reg` variable to a concrete hardware register.
In addition, it must respect architectural constraints imposed by the instruction set.
These constraints typically arise because certain assembly instructions:
- Require specific registers, or
- Impose equality constraints between source and destination registers.

For example:
```
 (of, cf2, sf, pf, zf, x) = #ADC_64(y, z, cf1);
```
The `ADC_64` instruction forces:
- The last argument `cf1` to be the carry flag `CF`,
- The first results `of, cf2, sf, pf, zf` to be the flags `OF, CF, SF, PF, ZF`,
- An additional constraint requiring the first source operand and the destination to use the same register;
  hence `x` and `y` must be allocated to the same register.

Due to these constraints, the following Jasmin program does not compile:
```
export fn fail(reg u64 y, reg u64 z) -> reg u64 {
  reg u64 x;
  x = y + z;
  x = x + y;
  return x;
}
```
Compilation fails with the following error:
```
compilation error:
register allocation: conflicting variables “y.230” and “x.237” must be merged due to:
  at "test.jazz", line 2 (2-12):
    ( _0.232,  _1.233,  _2.234,  _3.235,  _4.236, x.237) =
      #ADD_64(y.230, z.231); /*  */
  at "../test.jazz", line 3 (2-12):
    ( _5.238,  _6.239,  _7.240,  _8.241,  _9.242, x.243) =
      #ADD_64(x.237, y.230); /*  */
```
The first instruction enforces that `x.237` and `y.230` be merged into the same register.
However, both variables are live during the second instruction, which creates a conflict and makes the merge impossible.

To fix this, an explicit copy must be introduced:
```
export fn success(reg u64 y, reg u64 z) -> reg u64 {
  reg u64 x;
  x = y;
  x = x + z;
  x = x + y;
  return x;
}
```

## Finite number of registers

Because the number of registers is finite, there exist valid Jasmin programs that cannot be translated into assembly.

Consider the following example:
```
fn sum10 (reg u64 sum) -> reg u64 {
  inline int i;
  reg u64[14] t;
  for i = 0 to 14 {
    t[i] = i;
  }
  for i = 0 to 14 {
    sum += t[i];
  }
  return sum;
}

export fn test1 () -> reg u64 {
  reg u64 sum = 0;
  sum = sum10(sum);
  return sum;
}
```
This code compiles successfully. The function `sum10` uses 15 registers: one for sum and fourteen for the array `t`.

However, compilation may fail when sum10 is used in a different context:
```
fn sum10 (reg u64 sum) -> reg u64 {
  inline int i;
  reg u64[14] t;
  for i = 0 to 14 {
    t[i] = i;
  }
  for i = 0 to 14 {
    sum += t[i];
  }
  return sum;
}

export fn test1 () -> reg u64 {
  reg u64 sum = 0;
  sum = sum10(sum);
  return sum;
}

export fn test2() -> reg u64 {
  reg u64 j = 0;
  reg u64 sum = 0;
  while (j < 5) {
    sum = sum10(sum);
    j += 1;
  }
  return sum;
}
```
This results in the following error:
```
compilation error:
register allocation: no more free register to allocate variable:
    t#1.377 (defined at "../test.jazz", line 5 (4-5))
```
The issue arises because the variable `j` remains live throughout the execution of `sum10`, increasing register pressure.

One solution is to reduce the number of registers used by `sum10`. Another is to temporarily spill `j` to the stack:

```
export fn test3() -> reg u64 {
  stack u64 j_s;
  reg u64 j = 0;
  reg u64 sum = 0;

  while (j < 5) {
    j_s = j;
    sum = sum10(sum);
    j = j_s;
    j += 1;
  }
  return sum;
}
```
Here, the reg variable `j` is explicitly spilled to the stack variable `j_s` before the call to `sum10`, and unspilled afterward.

The same behavior can be expressed using the #spill and #unspill primitives:

the call to `sum10` and its value is recover (unspill) from memory after the call.
```
export fn test4() -> reg u64 {
  reg u64 j = 0;
  reg u64 sum = 0;

  while (j < 5) {
    #spill(j);
    sum = sum10(sum);
    #unspill(j);
    j += 1;
  }
  return sum;
}
```

## Constraints impose by function call

Function calls introduce additional register allocation constraints:
```
fn incr (reg u64 x1) -> reg u64 {
  x1 += 1;
  return x1;
}

export fn test (reg u64 x, reg u64 y) -> reg u64 {
  x = incr(x);
  y = incr(y);
  return y;
}
```
Compilation fails with:
```
compilation error:
register allocation: conflicting variables “x.237” and “y.238” must be merged due to:
  at "../test.jazz", line 2 (2-10):
    ( _0.232,  _1.233,  _2.234,  _3.235, x1.236) = #INC_64(x1.194); /*  */
  at "../test.jazz", line 7 (2-14):
    x.239 = incr(x.237);
  at "../test.jazz", line 8 (2-14):
    y.240 = incr(y.238);
```
Function calls introduce equality constraints between parameters
(respectively results) and arguments (respectively destinations).
In this example, these constraints force `x` and `y` to be allocated to the same register,
which is impossible since they are live simultaneously.
More precisly instruction `x.239 = incr(x.237)` generates constraints `x.239 = x1.236` and `x.237 = x1.194`
and instruction `y.240 = incr(y.238)` generates `y.240 = x1.236` and `y.238 = x1.194`.
So ``x.237` and `y.238` should be allocated in the same register but they are in live at the same time.

A solution is to introduce an explicit copy of `y`:
```
export fn test (reg u64 x, reg u64 y) -> reg u64 {
  x = incr(x);
  y = y;
  y = incr(y);
  return y;
}
```

## Using stable calling convention

Jasmin provides an experimental feature allowing the use of a predefined calling convention, customizable via function annotations.
This feature is only available for non-exported functions.

The general syntax is:
```
#[stable_call_conv = {reg = <int>, regx = <int>, xreg = <int>, flag = <int>} ]
```
This annotation specifies how many registers of each category may be used or modified by the function:
- `reg`  : general-purpose registers,
- `flag` : flag registers (x86 and ARM only),
- `regx` : MMX registers (x86 only),
- `xreg` : XMM/YMM registers (x86 only).

When `reg = n` is specified, the compiler conservatively assumes that the first `n` registers of that
category are modified by the function. Register names and order are fixed.

For x86 the four listes are
```
reg  ::= [RDI; RSI; RDX; RCX; R8; R9; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15]
regx ::= [MM0; MM1; MM2; MM3; MM4; MM5; MM6; MM7]
xreg ::= [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]
flag ::= [CF; PF; ZF; SF; OF]
```
For arm the listes are:
```
reg  ::= [R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12]
regx ::= []
xreg ::= []
flag ::= [CF; NF; ZF; VF ]
 ```

For riscv the listes are
```
reg  ::= [X10; X11; X12; X13; X14; X15; X16; X17; X5; X6; X7; X8; X9;
          X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30; X31 ]
regx ::= []
xreg ::= []
flag ::= []
```
Function arguments are forced to use the first registers of each category, and the same applies to return values.

The annotation can be partially specified, if only `#[stable_call_conv]` is provided this
is equivalent as using all registers of all categories.
When no integer arguments are provided to a category its means that all register of this category are used.
When a category is not provided its means that 0 register of this category is used.
For example, in x86:
```
#[stable_call_conv = {reg = 5, flag}]
```
is equivalent to
```
#[stable_call_conv = {reg = 5, flag = 5, regx = 0, xreg = 0}]
```

The following program uses a stable calling convention:
```
#[stable_call_conv = {reg = 5, flag = 5}]
fn f(reg u64 x1, reg u64 x2) -> reg u64 {
   reg u64 x3 = x1;
   x3 += x2;
   reg u64 x4 = x2;
   x4 += x3;
   reg u64 x5 = x4;
   x5 += x3;
   x5 += x4;
   x5 += x3;
   x5 += x2;
   x5 += x1;
   x5 = x5;
   return x5;
}

#[stable_call_conv = {reg = 5, flag}]
fn g1(reg u64 x1, reg u64 x2) -> reg u64 {
   #spill(x2);
   x1 = f(x1, x2);
   #unspill(x2);
   x1 += x2;
   return x1;
}

#[stable_call_conv = {reg = 6, flag}]
fn g2(reg u64 x1, reg u64 x2) -> reg u64 {
   reg u64 x3 = x2;
   x1 = f(x1, x2);
   x1 += x3;
   return x1;
}

export fn h (reg u64 x, reg u64 y, reg u64 w) -> reg u64 {
   reg u64 z;
   #spill(y);
   z = g1(x, y);
   #unspill(y);
   z = g2(z, y);
   z += w;
   return z;
}
```
Remark that the same program can be compiled without any need of spill or copy using the
customize calling convention of Jasmin.
```
fn f(reg u64 x1, reg u64 x2) -> reg u64 {
   reg u64 x3 = x1;
   x3 += x2;
   reg u64 x4 = x2;
   x4 += x3;
   reg u64 x5 = x4;
   x5 += x3;
   x5 += x4;
   x5 += x3;
   x5 += x2;
   x5 += x1;
   x5 = x5;
   return x5;
}

fn g1(reg u64 x1, reg u64 x2) -> reg u64 {
   x1 = f(x1, x2);
   x1 += x2;
   return x1;
}

export fn h (reg u64 x, reg u64 y, reg u64 w) -> reg u64 {
   reg u64 z;
   z = g1(x, y);
   z = g1(z, y);
   z += w;
   return z;
}
```





