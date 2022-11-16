(* Clear (overwrite) the stack before returning from export functions. *)

(* This pass is parameterized by one architecture-specific definition:
   - A piece of linear code that overwrites a number of bytes in the stack by
     iteratively clearing a fixed amount of bytes:
     [clear_stack_cmd : cs_strategy -> label -> wsize -> Z -> lcmd].

The linear command must implement the stack clearing depending on the chosen
strategy.
The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- Unrolled: Overwrite with a sequence of instructions (no loop).

In export functions we set the [total_stack] field to a multiple of the size
of a clearing step, so that the overwriting is done in an integer number of
writes. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Export clear_stack_strategy.
Require Import
  expr
  label
  linear
  sopn
  utils
  word
  wsize.
Require Import compiler_util linear_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

  Definition pass : string := "stack clearing".

  Definition error msg : pp_error_loc :=
    {|
      pel_msg := msg;
      pel_fn := None;
      pel_fi := None;
      pel_ii := None;
      pel_vi := None;
      pel_pass := Some pass;
      pel_internal := true;
    |}.

End E.


(* -------------------------------------------------------------------- *)
(* Architecture-specific parameters. *)
Record clear_stack_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    cs_clear_stack_cmd : cs_strategy -> label -> wsize -> wsize -> Z -> cexec lcmd;
  }.


Section CLEAR_STACK.

Context
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (css_of_fn : funname -> option (cs_strategy * wsize))
  (csparams : clear_stack_params).

Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).

Definition clear_stack_lfd_body lfd css ws : cexec lfundef :=
  let lbl := next_lfd_lbl lfd in
  let ws_align := lfd_align lfd in
  let max_stk_size := lfd_used_stack lfd in
  Let _ :=
    assert (is_align max_stk_size ws_align)
           (E.error
             (pp_box
               [:: pp_s "The max stack size ("; pp_z max_stk_size;
                   pp_s ") must be a multiple of the alignment of the stack (";
                   pp_s (string_of_wsize ws_align); pp_s ")"]))
  in
  Let _ :=
    assert (ws <= ws_align)%CMP
           (E.error
             (pp_box
               [:: pp_s "The clear step ("; pp_s (string_of_wsize ws);
                   pp_s ") should divide the alignment of the stack (";
                   pp_s (string_of_wsize ws_align); pp_s ")"]))
  in
  Let cmd := clear_stack_cmd css lbl ws_align ws max_stk_size in
  ok (map_lfundef (fun c => c ++ cmd) lfd).

Definition clear_stack_lfd fn (lfd : lfundef) : cexec lfundef :=
  if css_of_fn fn is Some (css, ws)
  then
    if lfd_export lfd && (0 <? lfd_used_stack lfd)%Z
    then clear_stack_lfd_body lfd css ws
    else ok lfd
  else
    ok lfd.

Definition clear_stack_lprog (lp : lprog) : cexec lprog :=
  Let lp_funs := map_lprog_name clear_stack_lfd lp.(lp_funcs) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_funcs := lp_funs;
    |}.

End CLEAR_STACK.
