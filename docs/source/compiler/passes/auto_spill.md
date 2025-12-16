# Automated spilling

This is an experimental feature of the `jasminc` command-line tool, enabled
using either `-auto-spill` or `-auto-spill-all`. This trusted program
transformation inserts unspill operations before every use of a variable and
spill operations after every definition of a variable.

Variables that are subject to this transformation are variables of kind `reg`
and of machine-word type.

When using `-auto-spill`, only variables that are declared with a `spill`
annotation are subject to this transformation.

For instance, in the following program, two spilling operations are introduced,
after each write to the variable `i`: once before the loop and once at the end
of the loop body. Moreover, two unspill operations are introduced, before each
read from the variable `i`: once within the loop body before the increment and
once before evaluating the loop guard.

~~~
export
fn main(reg u32 arg) -> reg ui32 {
  arg &= 0x1f;
  reg ui32 result = 1;
  #[spill] reg u32 i = 0;
  while (i < arg) {
    result <<= 1;
    i += 1;
  }
  return result;
}
~~~

When using `-auto-spill-all`, all such variables are spilled and unspilled,
except the ones declared with an explicitly `nospill` annotation.

In the example program below, when using `-auto-spill-all`, the pointer argument
is spilled on function entry and unspilled before both accesses to its contents.
The other local variables `x`, `y`, and `z` are annotated `nospill`: therefore
no spill or unspill operation related to them is introduced.

~~~
export
fn xor(reg ptr u32[2] arg) -> reg u32 {
  #[nospill]
  reg u32 x y z;
  x = arg[0];
  y = arg[1];
  z = x ^ y;
  return z;
}
~~~

Automated spilling can be disabled in a whole function by annotating said
function as `nospill`.

A `msf` annotation is treated as a `nospill` annotation.
