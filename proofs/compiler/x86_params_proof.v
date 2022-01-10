From mathcomp Require Import all_ssreflect all_algebra.
Require Import linearization_proof sopn psem compiler compiler_proof.
Require Import
  x86_decl
  x86_instr_decl
  x86_extra
  x86_linearization_proof
  x86_stack_alloc_proof.
Require Import x86_params.
Require x86_gen_proof.
Require lowering_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x86_is_move_opP : forall op vx v,
  is_move_op x86_params op ->
  exec_sopn (Oasm op) [:: vx] = ok v ->
  List.Forall2 value_uincl v [:: vx].
Proof.
  by case=> // -[] []// []//= ws vx v _;
    rewrite /exec_sopn /=;
    t_xrbindP=> w ? /to_wordI [ws' [wx [hle -> ->]]];
    rewrite /sopn_sem /=;
    match goal with
    | |- ?f (zero_extend _ _) = _ -> _ => rewrite /f
    end;
    t_xrbindP=> _ _ <- <-;
    (constructor; last by constructor);
    apply value_uincl_zero_ext.
Qed.

Lemma ok_x86_lp_tmp :
  exists r : reg_t, of_string (lp_tmp (lparams x86_params)) = Some r.
Proof.
  exists RAX.
  rewrite /=.
  change "RAX"%string with (to_string RAX).
  exact: to_stringK.
Qed.


Definition x86_hyps : architecture_hyps x86_params :=
  {| is_move_opP := x86_is_move_opP
   ; lower_callP := lowering_proof.lower_callP
   ; mov_ofsP := x86_mov_ofsP
   ; hlparams := h_x86_linearization_params
   ; assemble_cond := x86_gen.assemble_cond
   ; eval_assemble_cond := x86_gen_proof.eval_assemble_cond
   ; assemble_extra_op := x86_gen_proof.assemble_extra_op
   ; assemble_progP := x86_gen_proof.assemble_progP
   ; ok_lp_tmp := ok_x86_lp_tmp
  |}.
