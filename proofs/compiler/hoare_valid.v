Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  psem
  psem_facts
  core_logics
  relational_logic
  low_memory
.

Require Import
  xrutt
  xrutt_facts.

Section HOARE.

Context
  {wa : WithAssert}
  {wsw:WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT: progT} {scP: semCallParams}
  {E E0: Type -> Type}
  {wE: with_Error E E0}
  {rE : RndEvent syscall_state -< E}
  {iE0 : InvEvent E0}
  {iEr : InvErr}
.

Lemma hoare_f_body_validw_stable (p : prog (pT := pT)) ev fn ii :
  hoare_f_ii (sem_F := sem_fun_full) p ev
    (fun _ => PredT)
    ii fn
    (fun _ fs fs' => validw (fmem fs) =3 validw (fmem fs')).
Proof using. Admitted.

End HOARE.

