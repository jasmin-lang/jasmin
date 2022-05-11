From mathcomp Require Import all_ssreflect all_algebra.
Require Import sopn psem compiler_proof.
Require Import x86_decl x86_instr_decl x86_extra.
Require Import x86_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma is_move_opP : forall op vx v,
  is_move_op op ->
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

Definition ahyps :=
  @mk_ahyps aparams is_move_opP.
