# Compilation passes

As any compiler, the Jasmin compiler is organized as a succession of compiler
passes. Here is a representation of the current compilation pipeline. Note
that a few passes appear several times.

:::{graphviz} passes.dot
:::

:::{tip}
You can click on a pass to access its dedicated page.
:::

The particularity of the Jasmin compiler is of course that it is formally
proved correct. Each pass falls into one of the three following categories.
- It is proved: this is the case for most of the passes. The pass is written
  and proved correct in the Rocq Prover.
- It is validated: another approach to prove the correctness of a pass is
  so-called a posteriori validation. Instead of proving the pass, we prove
  a checker that is run after the pass and validates that what the pass did
  is correct. Typically, in this case, the pass is written in OCaml (and not
  proved), and the checker is written and proved in Rocq.
- It is trusted: nothing is actually proved about the pass, because it is
  not clear what could be proved about it and/or it is simple enough.
  The pass is then part of the Trusted Computing Base.

Here is a list of the passes with a short description of what each does.
Each pass is described in more detail on a dedicated page.

- [Replace word ints](wint_word) replaces word-sized integers with machine words
- [Insert renaming](insert_renaming) introduces renaming assignments at export function boundaries
- [Array copy](array_copy) expands `#copy` operations into explicit `for` loops
- [Array init](array_init) inserts array-init instructions at the beginning of functions
- [Lowering of spills](lower_spill) replaces `#spill` and `#unspill` operations
  with standard copies respectively from `reg` to `stack` variables and from `stack`
  to `reg` variables
- [Function inlining](function_inlining) inlines calls to `inline` functions
  and calls annotated with `#inline`
- [Function pruning](removal_unused_functions)
  removes unused functions, i.e. non-export functions not called from an export
  function; in particular,`inline` functions are unused after inlining
- [Constant propagation](constant_propagation) replaces some variables known
  to be constant with the corresponding constants
- [Dead-code elimination](deadcode_elimination) eliminates dead code, i.e. code
  that has no effect on the return values of the function
- [Loop unrolling](loop_unrolling) unrolls systematically `for` loops,
  replacing them with copies of the loop body
- [Live-range splitting](liverange_splitting) reduces the liverange of
  variables by renaming variables when they are assigned
- [Remove array init](array_init_rm) removes array-init instructions
- [Make ref arguments](make_ref_arguments)
  inserts `ptr` intermediate variables for function arguments and returned values
- [Reg. array expansions](expansion_reg_arrays)
  makes each cell of `reg` arrays an independent variable
- [Remove globals](remove_global) turn `global` local variables into proper global values
- [Load constants (RISC-V)](load_constants) replaces constants appearing in
  conditions with `reg` variables set to these constants (on RISC-V only)
- [Instruction selection](inst_select), aka lowering, replaces high-level
  instructions with assembly instructions from the target architecture
- [Inline propagation](propagate_inline) propagates variables marked as `inline`;
  it is particularly useful to deal with expressions made of flags
- [SLH](lower_slh) replaces SLH operators with their implementations in the
  target architecture
- [Stack allocation](stack_alloc) replaces stack variables with memory accesses
- [Lower addr. (RISC-V)](lower_addr) turns complex memory accesses, not compilable
  as is on RISC-V, into several simpler instructions (on RISC-V only)
- [Remove unused returned values](rm_unused_ret_value)
  removes from functions the results that are not used, i.e. not needed by an
  export function
- [Register allocation](reg_alloc) replaces `reg` variables with registers
  from the current architecture, or fails if it does not manage to do so
- [One varmap](merge_varmaps) checks that compilation can proceed
- [Linearization](linearization) does two things: it introduces explicit code
  for handling the stack and function arguments, and replaces the structured
  control flow with labels & gotos
- [Tunneling](tunneling) removes unneeded chain of gotos
- [ASM generation](asm_gen) generates the assembly

:::{toctree}
:hidden:

wint_word
insert_renaming
array_copy
array_init
lower_spill
function_inlining
removal_unused_functions
constant_propagation
deadcode_elimination
loop_unrolling
liverange_splitting
make_ref_arguments
array_init_rm
expansion_reg_arrays
remove_global
load_constants
inst_select
propagate_inline
lower_slh
stack_alloc
lower_addr
rm_unused_ret_value
reg_alloc
merge_varmaps
linearization
stack_zero
tunneling
asm_gen
:::
