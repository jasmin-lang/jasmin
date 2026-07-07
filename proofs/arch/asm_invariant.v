From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  utils
  core_logics
  syscall
  syscall_sem
  memory_model
  global
  oseq
  sem_type
  label
  arch_decl
.
Require Import
  arch_decl
  arch_extra
  arch_sem
.
Require Export it_sems_core_defs.
Require Import it_sems_core.

Section WITH_PARAMS.

Context
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
.

#[local] Existing Instance asmsem_invariant_Equiv.

Lemma iasmsem_exportcall_invariantP
  (xp : asm_prog) (fn : funname) (xm : asmmem) :
  lutt (fun T (_ : E T) => True)
       (fun T (_ : E T) (_ : T) => True)
       (fun xm' => asmsem_invariant xm xm')
       (iasmsem_exportcall xp fn xm).
Proof.
  rewrite /iasmsem_exportcall.
  apply: (lutt_bind (R := fun _ => True)).
  - exact: lutt_true.
  move=> fd _.
  apply: (lutt_bind (R := fun _ => True)).
  - exact: lutt_true.
  move=> _ _.
  apply: (lutt_bind (R := fun _ => True)).
  - exact: lutt_true.
  move=> _ _.
  apply: (lutt_bind (R := fun s' => asmsem_invariant xm s'.(asm_m))).
  - apply: (lutt_iter (I := fun s => asmsem_invariant xm s.(asm_m))) => //.
    move=> s hI.
    rewrite /iasmsem_body /while.while_body.
    case: ifP => _.
    * cbn; apply lutt_Ret; exact: hI.
    apply: (lutt_bind (R := fun s' => asmsem_invariant xm s'.(asm_m))).
    -- rewrite /ifetch_and_eval.
       case h: (fetch_and_eval xp s) => [s' | e].
       ++ apply lutt_Ret.
          etransitivity; first exact: hI.
          exact: fetch_and_eval_invariant h.
       by apply: lutt_Vis => //; case.
    move=> s' hs'; cbn; apply lutt_Ret; exact: hs'.
  move=> t1 hs'.
  apply: (lutt_bind (R := fun _ => True)).
  - exact: lutt_true.
  move=> _ _; apply lutt_Ret; exact: hs'.
Qed.

End WITH_PARAMS.
