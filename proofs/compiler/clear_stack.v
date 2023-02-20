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
Require Import one_varmap.

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
    cs_clear_stack_cmd :
      cs_strategy -> (* clearing strategy : while or for loop *)
      var_i ->       (* RSP *)
      label ->       (* fresh label *)
      wsize ->       (* stack alignment *)
      wsize ->       (* clearing step *)
      Z ->           (* stack size to be cleared *)
      cexec lcmd;
  }.


Section CLEAR_STACK.

Context
  {pd: PointerData}
  {asm_op : Type} {asmop: asmOp asm_op}
  {ovmi : one_varmap_info}
  (csparams : clear_stack_params)
  (css_of_fn : funname -> option (cs_strategy * wsize)).

Notation clear_stack_cmd := (cs_clear_stack_cmd csparams).

Definition write_i_rec s (i:linstr_r) :=
  match i with
  | Lopn xs _ _ => vrvs_rec s xs
  | Lsyscall _ => s
  | Lcall _ => s
  | Lret => s
  | Lalign   => s
  | Llabel _ _ => s
  | Lgoto d => s
  | Ligoto e => s
  | LstoreLabel x lbl => Sv.add x s
  | Lcond e lbl => s
  end.

Definition write_I_rec s i :=
  match i with
  | MkLI _ i => write_i_rec s i
  end.
(*
Definition write_i i := write_i_rec Sv.empty i.

Definition write_I i := write_I_rec Sv.empty i.
*)
Definition write_c_rec s c := foldl write_I_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

(*
Definition local_code lbls (i : linstr) :=
  match li_i i with
  | Lopn _ _ _ | Llabel _ _ => true
  | Lcond _ lbl => lbl \in lbls
  | _ => false
  end.

Lemma test lp c : local_code c ->
  lsem lp (of_estate s fn pc) (of_estate ) ->
  vm = vm' [\ write_c c].
*)
(* TODO : get rid of WArray.PointerZ ! *)
Definition clear_stack_lfd_body rsp lfd css ws : cexec lfundef :=
  let lbl := next_lfd_lbl lfd in
  let ws_align := lfd_align lfd in
  let frame_size := lfd_frame_size lfd in
  let used_stk := lfd_used_stack lfd in
  Let _ :=
    assert (is_align (Pointer:=WArray.PointerZ) frame_size ws_align)
           (E.error
             (pp_box
               [:: pp_s "The export frame size ("; pp_z frame_size;
                   pp_s ") must be a multiple of the alignment of the stack (";
                   pp_s (string_of_wsize ws_align); pp_s ")"]))
  in
  Let _ :=
    assert (is_align (Pointer:=WArray.PointerZ) used_stk ws)
           (E.error
             (pp_box
               [:: pp_s "The used stack size ("; pp_z used_stk;
                   pp_s ") must be a multiple of the clear step (";
                   pp_s (string_of_wsize ws); pp_s ")"]))
  in
  Let _ :=
    assert (ws <= ws_align)%CMP
           (E.error
             (pp_box
               [:: pp_s "The clear step ("; pp_s (string_of_wsize ws);
                   pp_s ") should divide the alignment of the stack (";
                   pp_s (string_of_wsize ws_align); pp_s ")"]))
  in
  Let cmd := clear_stack_cmd css rsp lbl ws_align ws used_stk in
  Let _ :=
    let vars := write_c cmd in
    assert (disjoint vars (Sv.union callee_saved (sv_of_list v_var lfd.(lfd_res))))
           (E.error (pp_box [:: pp_s "clash"]))
  in
  ok (map_lfundef (fun c => c ++ cmd) lfd).

Definition clear_stack_lfd rsp fn (lfd : lfundef) : cexec lfundef :=
  let ws_align := lfd_align lfd in
  let used_stk := lfd_used_stack lfd in
  if css_of_fn fn is Some (css, ws)
  then
    if lfd_export lfd && (0 <? lfd_used_stack lfd)%Z
    then
      clear_stack_lfd_body rsp lfd css ws
    else ok lfd
  else
    ok lfd.

Definition clear_stack_lprog (lp : lprog) : cexec lprog :=
  (* This ensures that sp is callee saved and thus has same value at the end
     of the body as at the start. Could probably be derived from the proof
     of the previous passes.
  *)
(*   Let _ := assert (Sv.mem (vid lp.(lp_rsp)) callee_saved)
                  (E.error (pp_s "rsp is not callee saved")) *)
(*   in *)
  Let lp_funs := map_lprog_name (clear_stack_lfd (vid lp.(lp_rsp))) lp.(lp_funcs) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_funcs := lp_funs;
    |}.

End CLEAR_STACK.
