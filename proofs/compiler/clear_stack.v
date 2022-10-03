(* Clear (ovewrite) the stack before returning from export functions. *)

(* This pass is parameterized by two architecture-specific definitions:
   - The maximum amount of bits we can write to the stack in one instruction:
     [max_sz : wsize].
   - A piece of linear code that ovewrites a number of bytes in the stack:
     [clear_stack_cmd : cs_strategy -> label -> Z -> lcmd].

The linear command must implement the stack clearing depending on the chosen
strategy.
The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- Unrolled: Overwrite with a sequence of instructions (no loop).

In export functions we set the [total_stack] field to a multiple of [max_sz]
so that the overwriting is done in an integer number of writes. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Export clear_stack_strategy.
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

Module E.

  Definition pass : string := "stack clearing".

  Definition css_error (fn : funname) : pp_error_loc :=
    {|
      pel_msg := PPEstring "Invalid strategy";
      pel_fn := Some fn;
      pel_fi := None;
      pel_ii := None;
      pel_vi := None;
      pel_pass := Some pass;
      pel_internal := false;
    |}.

End E.


(* -------------------------------------------------------------------- *)
(* Architecture-specific parameters. *)
Record clear_stack_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    cs_max_ws : wsize;
    cs_clear_stack_cmd : cs_strategy -> label -> Z -> option lcmd;
  }.


Section CLEAR_STACK.

Context
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (css_of_fn : funname -> option cs_strategy)
  (csparams : clear_stack_params).

Notation max_ws := (cs_max_ws csparams).
Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).

Definition lfd_clear_stack
  (s : cs_strategy) (lbl : label) (lfd : lfundef) : option (lfundef * label) :=
  if clear_stack_cmd s lbl (lfd_used_stack lfd) is Some tail
  then
    let lfd' := map_lfundef (fun c => c ++ tail) lfd in
    Some (lfd', next_lbl lbl)
  else
    None.

Definition prog_clear_stack_aux
  (lbl : label) (fn : funname) (fd : lfundef) : cexec (lfundef * label) :=
  if css_of_fn fn is Some css
  then
    if lfd_export fd && (0 <? lfd_used_stack fd)%Z
    then o2r (E.css_error fn) (lfd_clear_stack css lbl fd)
    else ok (fd, lbl)
  else
    ok (fd, lbl).

Definition accf '(fn, lfd) '(lfds, lbl) :=
  Let: (lfd', lbl') := prog_clear_stack_aux lbl fn lfd in
  ok (lfds ++ [:: (fn, lfd') ], lbl').

Definition prog_clear_stack (lp : lprog) : cexec lprog :=
  Let: (fs', _) := foldM accf ([::], next_lprog_lbl lp) (lp_funcs lp) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_funcs := fs';
    |}.

End CLEAR_STACK.
