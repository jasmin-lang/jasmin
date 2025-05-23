# How to execute the formal semantics

The semantics of the Jasmin programming language is formally defined in Coq, as
a big-step inductive relation, is the `sem` module. An equivalent definition is
given as an OCaml recursive function in the `Evaluator` module.

A Jasmin program is a collection of function definitions: it does not make much
sense to *execute* such a program. However, the interpreter can execute a call
to a function applied to some arguments from some initial memory.

The evaluator runs before the compilation and evaluates all `exec` directives
found in the file being compiled (if any).
Such a directive starts with the `exec` keyword, followed by the name of the function to call,
followed by a description of the initial memory layout.

NB: currently, there is no concrete syntax to describe the function arguments;
the function to interpret must have no parameter. However, it is possible to write
an auxiliary function that computes the arguments for the function to evaluate.

Here is a complete example.

~~~
param int N = 4;

fn zero() -> reg u64[N] {
  inline int i;
  reg u64[N] t;
  for i = 0 to N {
    t[i] = i;
  }
  return t;
}

exec zero()
~~~

When running the `jasminc` compiler on this program, the following is
displayed on the standard output:

> Evaluation of zero ():
> [0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0; 0; 0; 0; 0]

Notice that the returned result is pretty-printed using hexadecimal numbers, and
that arrays are shown as arrays of `u8` (this reveals the endianness of the array).

## Initial memory layout

If the function to evaluate accesses (reads from or writes to) the memory,
the interpreter must be run from a state that has enough valid regions.

At the end of an `exec` directive, the parentheses enclose a list of valid address ranges.
Ranges are separated by commas `,` and are given as a pair `start-address : length`.

NB: these declared valid regions are not initialized; the function to be
evaluated should write the memory before reading it.

For instance, the evaluation of the following program displays:
“Evaluation of mem (4096:8): FF”.

~~~
inline
fn mem() -> reg u64 {
  reg u64 r;
  reg u64 p;

  p = 0x1000;

  [ p + 0] = 255;
  r = [ p + 0];

  return r;
}

exec mem (0x1000 : 8)
~~~
