(* Zeroize the stack before returning from export functions. *)

(* This pass is parameterized by one architecture-specific definition:
   - A piece of linear code that overwrites a number of bytes in the stack by
     iteratively clearing a fixed amount of bytes:
     [stack_zeroization_cmd : cs_strategy -> label -> wsize -> Z -> lcmd].

The linear command must implement the stack zeroization depending on the chosen
strategy (see [lang/stack_zero_strategy.v]).

In export functions we set the [stk_max] field to a multiple of the size
of a clearing step, so that the overwriting is done in an integer number of
writes. *)

From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import word_ssrZ.
Require Import ZArith.

Require Import
  expr
  label
  linear
  sopn
  utils
  word
  wsize.
Require Import compiler_util linear_util.
Require Import one_varmap.
Require Export stack_zero_strategy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

  Definition pass : string := "stack zeroization".

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
Record stack_zeroization_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    szp_cmd :
      stack_zero_strategy -> (* zeroization strategy *)
      Ident.ident ->         (* RSP *)
      label ->               (* fresh label *)
      wsize ->               (* stack alignment *)
      wsize ->               (* clearing step *)
      Z ->                   (* stack size to be zeroized *)
      cexec (lcmd * Sv.t);
        (* the command and the set of written variables in the command (except RSP) *)
  }.


Section STACK_ZEROIZATION.

Context
  {pd: PointerData}
  {asm_op : Type} {asmop: asmOp asm_op}
  {ovmi : one_varmap_info}
  (szparams : stack_zeroization_params)
  (szs_of_fn : funname -> option (stack_zero_strategy * wsize)).

Notation stack_zeroization_cmd := (szp_cmd szparams).

Definition stack_zeroization_lfd_body (rspn:Ident.ident) lfd szs ws : cexec lfundef :=
  let lbl := next_lfd_lbl lfd in
  let ws_align := lfd_align lfd in
  let frame_size := lfd_frame_size lfd in
  let stk_max := lfd_stk_max lfd in
  Let _ :=
    assert (is_align frame_size ws_align)
           (E.error
             (pp_box
               [:: pp_s "The export frame size ("; pp_z frame_size;
                   pp_s ") must be a multiple of the alignment of the stack (";
                   pp_s ("u" ++ string_of_wsize ws_align); pp_s ")"]))
  in
  Let _ :=
    assert (is_align stk_max ws)
           (E.error
             (pp_box
               [:: pp_s "The used stack size ("; pp_z stk_max;
                   pp_s ") must be a multiple of the clear step (";
                   pp_s ("u" ++ string_of_wsize ws); pp_s ")"]))
  in
  Let _ :=
    assert (ws <= ws_align)%CMP
           (E.error
             (pp_box
               [:: pp_s "The clear step ("; pp_s (string_of_wsize ws);
                   pp_s ") should divide the alignment of the stack (";
                   pp_s ("u" ++ string_of_wsize ws_align); pp_s ")"]))
  in
  Let: (cmd, vars) := stack_zeroization_cmd szs rspn lbl ws_align ws stk_max in
  Let _ :=
    assert (~~ Sv.mem (vid rspn) vars)
           (E.error
             (pp_box
               [:: pp_s "RSP modified"]))
  in
  Let _ :=
    assert (disjoint vars (Sv.union callee_saved (sv_of_list v_var lfd.(lfd_res))))
           (E.error
             (pp_box
               [:: pp_s "The zeroization code modified registers that should be";
                   pp_s "unchanged per the calling conventions"]))
  in
  ok (map_lfundef (fun c => c ++ cmd) lfd).

Definition stack_zeroization_lfd rsp fn (lfd : lfundef) : cexec lfundef :=
  if szs_of_fn fn is Some (szs, ws)
  then
    if lfd_export lfd && (0 <? lfd_stk_max lfd)%Z
    then
      stack_zeroization_lfd_body rsp lfd szs ws
    else ok lfd
  else
    ok lfd.

Definition stack_zeroization_lprog (lp : lprog) : cexec lprog :=
  Let lp_funs := map_cflprog_name (stack_zeroization_lfd lp.(lp_rsp)) lp.(lp_funcs) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_glob_names := lp_glob_names lp;
      lp_funcs := lp_funs;
    |}.

End STACK_ZEROIZATION.
