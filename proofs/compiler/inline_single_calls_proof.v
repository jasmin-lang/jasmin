From Coq Require Import ZArith.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  psem
  compiler_util.
Require
  inline_proof
  dead_calls_proof.
Require Export inline_single_calls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local]
Existing Instance indirect_c.

Lemma isc_prog_sem_call
  single_calls rename_fd to_keep p p' fn ev scs mem scs' mem' va va' vr :
  isc_prog single_calls rename_fd to_keep p = ok p' ->
  fn \in to_keep ->
  List.Forall2 value_uincl va va' ->
  sem_call p ev scs mem fn va scs' mem' vr ->
  exists2 vr',
    List.Forall2 value_uincl vr vr'
    & sem_call p' ev scs mem fn va' scs' mem' vr'.
Proof.
  rewrite /isc_prog.
  case: nilp.
  - move=> [->] _ h0 h1. have [? []] := sem_call_uincl h0 h1. by eauto.

  t_xrbindP=> p0 hinline hdeadcalls hto_keep hargs hcall.
  have [? [hcall' ?]] := inline_proof.inline_call_errP hinline hargs hcall.
  have := dead_calls_proof.dead_calls_err_seqP hdeadcalls hto_keep hcall'.
  by eauto.
Qed.

End WITH_PARAMS.
