From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import
  expr
  memory_model
  psem
  stack_alloc_proof_2.
Require Import arm_decl arm_stack_alloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ARM_PROOF.

  Context
    (P' : sprog)
    (P'_globs : P'.(p_globs) = [::]).

  Lemma addiP s1 e i x tag ofs w s2 :
    sem_pexpr [::] s1 e >>= to_pointer = ok i ->
    write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
    sem_i P' w s1 (addi x tag e ofs) s2.
  Proof.
    move=> he hx.
    apply Eopn.
    rewrite /sem_sopn /= P'_globs /exec_sopn /=.
    move: he.
    t_xrbindP=> _ -> /= -> /=.
    by rewrite hx.
  Qed.

End ARM_PROOF.

Lemma arm_mov_ofsP (P': sprog) s1 e i x tag ofs w vpk s2 ins :
  P'.(p_globs) = [::] ->
  sem_pexpr [::] s1 e >>= to_pointer = ok i ->
  arm_mov_ofs x tag vpk e ofs = Some ins ->
  write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2 ->
  sem_i P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /arm_mov_ofs.
  move=> [<-].
  by apply addiP.
Qed.
