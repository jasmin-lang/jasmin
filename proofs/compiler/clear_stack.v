(* Clear (ovewrite with zeroes) the stack before returning from export
   functions. *)

(* This pass is parameterized by two architecture-specific definitions:
   - The maximum amount of zeroes we can write to the stack in one
     instruction: [max_sz : wsize].
   - A piece of linear code that ovewrites a number of bytes in the stack
     with zeroes: [clear_stack_loop : label -> Z -> lcmd].

In export functions we set the [total_stack] field to a multiple of [max_sz]
so that the overwriting is done in an integer number of writes.
The linear command might use a loop to implement this, so it is provided
with a [label]. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Import
  compiler_util
  expr
  label
  linear
  sopn
  utils
  word
  wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Architecture-specific parameters. *)
Record clear_stack_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    cs_max_ws : wsize;
    cs_clear_stack_loop : label -> Z -> lcmd;
  }.


Section CLEAR_STACK.

Context
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (csparams : clear_stack_params).

Notation max_ws := (cs_max_ws csparams).
Notation clear_stack_loop := (cs_clear_stack_loop csparams).

Definition lfd_clear_stack (lbl : label) (lfd : lfundef) : lfundef * label :=
  let (tail, lbl') :=
    if lfd_export lfd
    then (clear_stack_loop lbl (lfd_total_stack lfd), next_lbl lbl)
    else ([::], lbl)
  in
  let lfd' :=
    {|
      lfd_info := lfd_info lfd;
      lfd_align := lfd_align lfd;
      lfd_tyin := lfd_tyin lfd;
      lfd_arg := lfd_arg lfd;
      lfd_tyout := lfd_tyout lfd;
      lfd_total_stack := lfd_total_stack lfd;
      lfd_res := lfd_res lfd;
      lfd_export := lfd_export lfd;
      lfd_callee_saved := lfd_callee_saved lfd;
      lfd_body := lfd_body lfd ++ tail;
    |}
  in
  (lfd', lbl').

Definition prog_clear_stack (lp : lprog) : lprog :=
  let f '(lfds, lbl) '(fn, fd) :=
    let '(lfd', lbl') := lfd_clear_stack lbl fd in
    (lfds ++ [:: (fn, lfd') ], lbl')
  in
  {|
    lp_rip := lp_rip lp;
    lp_rsp := lp_rsp lp;
    lp_globs := lp_globs lp;
    lp_funcs := (foldl f ([::], next_lprog_lbl lp) (lp_funcs lp)).1;
  |}.

End CLEAR_STACK.
