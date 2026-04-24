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
  {wsw:WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0: Type -> Type}
  {wE: with_Error E E0}
  {rE : RndEvent syscall_state -< E}
.

#[local] Existing Instance trivial_invErr.
#[local] Existing Instance trivial_invEvent.
#[local] Existing Instance noassert.

Lemma sem_fun_full_unfold p ev ii fn fs :
  eutt eq
    (sem_fun_full.(sem_fun) p ev ii fn fs)
    (isem_fun_body (sem_F := sem_fun_full) p ev fn fs).
Proof.
rewrite /= /isem_fun /isem_fun_def mrec_as_interp interp_bind interp_ioget.
apply: eutt_eq_bind => fd /=; rewrite interp_bind /= interp_iresult.
apply: eutt_eq_bind => _; rewrite interp_bind /= interp_iresult.
apply: eutt_eq_bind => s; rewrite interp_bind /isem_cmd_ -interp_isem_cmd.
apply: eutt_eq_bind => s'; rewrite interp_bind interp_iresult.
apply: eutt_eq_bind => fs'; rewrite interp_bind interp_iresult.
apply: eutt_eq_bind => _; rewrite interp_ret.
reflexivity.
Qed.

Section PROOF.

Context {pT: progT} {scP: semCallParams}.

Let MemEquivSpec : HoareSpec :=
  {|
    preF_ := relT;
    postF_ := fun _ fs fs' => mem_equiv (fmem fs) (fmem fs');
  |}.

Lemma sem_fun_mem_equiv p ev fn ii :
  (forall s1 s2 m2 ef,
      init_state ef p.(p_extra) ev s1 = ok s2 ->
      mem_equiv (emem s2) m2 ->
      mem_equiv (emem s1) (finalize ef m2)) ->
  hoare_f_ii (sem_F := sem_fun_full) p ev
    relT
    ii fn
    (fun _ fs fs' => mem_equiv (fmem fs) (fmem fs')).
Proof.
move=> h fs _.
apply: (ihoare_fun (spec := MemEquivSpec) (Qerr := PredT) _ I) =>
  _ {}fn {}fs _; split=> //.
case hget: get_fundef => [fd|//]; split=> //.
exists
  (fun s => mem_equiv (fmem fs) (emem s)),
  (fun s => mem_equiv (fmem fs) (emem s));
  split=> //.
- move=> fs' _; case hi: initialize_funcall => [s|//].
  move: hi; rewrite /initialize_funcall; t_xrbindP=> vs hvs s' /h {}h hw.
  admit.
  admit.
move=> s heq; case hf: finalize_funcall => [fs'|//].
move: hf; rewrite /finalize_funcall; t_xrbindP=> _ _ _ _ <- /= {fs'}.
Admitted.

End PROOF.

Lemma sem_fun_mem_equiv_uprog (p : uprog) ev fn ii :
  hoare_f_ii (sem_F := sem_fun_full) p ev
    relT
    ii fn
    (fun _ fs fs' => mem_equiv (fmem fs) (fmem fs')).
Proof. by apply: sem_fun_mem_equiv => s1 s2 m2 ef /= [<-]. Qed.

Lemma sem_fun_mem_equiv_sprog (p : sprog) ev fn ii :
  hoare_f_ii (sem_F := sem_fun_full) p ev
    relT
    ii fn
    (fun _ fs fs' => mem_equiv (fmem fs) (fmem fs')).
Proof.
apply: sem_fun_mem_equiv => s1 s2 m2 ef /=.
rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

End HOARE.

