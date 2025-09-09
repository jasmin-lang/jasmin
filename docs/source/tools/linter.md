# Linting Jasmin programs

The Jasmin compiler performs, on demand, a few checks in order to detect a few
programming errors. These checks are performed early in the compilation process
(right after type-checking) and aim at producing reliable diagnostics.

## Usage

The linter is available through the `jasmin.linter` OCaml library and is also
integrated into the `jasminc` program. This section describes this integration
only.

The interface to the linter is still considered experimental and subject to
change.

The `--linting-level n` command-line arguments controls which issues are
reported. Its argument `n` takes a numerical value, from zero (0) to two (2). At
level zero, no issue are reported (and the linter does not even run). At level
one, the default, severe issues are reported: users are advised to fix such
issues as soon as possible. At level two, some less severe issues are also
reported.

1. Level 1 reports:
  - Variables used without initialization
  - Instructions assigning dead variables only
2. Level 2 also reports:
  - Dead variables assigned within an instruction that has other effects

## Uses of uninitialized variables

This checker ensures that every variable may be initialized before use and
reports uses of variables that are never initialized.

An example mistake reported by this check follows. There, the first assignment
to `x` should be unconditional.

~~~
fn wrong_init_if(reg bool b) -> reg u32 {
  reg u32 x;
  x = 0 if b;
  x = 0 if !b;
  return x;
}
~~~

This checker never raises false alarms. Therefore, it does not attempt at
detecting more subtle issues, such as the one occurring in the example below (if
the `bound` argument is zero, the loop does not execute, and the returned
variable `r` is not initialized). To this end, rather use a safety checker.

~~~
fn init_in_loop(reg u32 bound) -> reg u32 {
  reg u32 i, r;
  i = 0;
  while (i < bound) {
    i += 1;
    r = 0;
  }
  return r;
}
~~~

## Assignments to dead variables

This checker aims at detecting dead code. It warns about instructions that
assign variables that are never used afterwards and has no other effect.
A simple example of error detected by this checker is a forgotten return:

~~~
inline fn dead_stack_array(stack u8[1] p) {
  p[0] = 0; // this instruction is dead; a warning is raised
}
~~~

This check is not “transitive”: variables that are used in dead instructions are
not reported as dead. For instance in the example below, only one warning is
raised, about the assignment to `k`.

~~~
fn dead_sequence(reg u32 i) {
  reg u32 j = i;
  reg u32 k = j; // although this is dead code, it counts as a use of j
}
~~~

The granularity of this checker is the variable. Therefore it does not finely
track the liveness of individual array cells. For instance in the example below,
the assignment to the second cell of the array is dead but will not raise any
warning.

~~~
fn dead_cell(reg u32 a) -> reg u32 {
  reg u32[2] r;
  r[0] = a;
  r[1] = a; // this is dead code, but variable r is live
  reg u32 b = r[0];
  return b;
}
~~~

A stricter form of this checker exists and is enabled at level 2, but may raise false alarms.
It warns about instructions that assign to dead variables but are not themselves dead
(because they, e.g., also assign live variables, or write to the user memory, etc.). For instance
it will report in the example below that the last assignment to `z` is dead.

~~~
fn only_one_live_result(reg u64 x) -> reg u64 {
  reg u64 z = 0;
  x, z = #swap(z, x); // z is assigned but never used afterwards
  return x;
}
~~~
