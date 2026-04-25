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
  {E E0: Type -> Type}
  {wE: with_Error E E0}
  {rE : RndEvent syscall_state -< E}
  {iEr : InvErr}
  {iE0 : InvEvent E0}
.

Section PROOF.

Context
  {pT : progT}
  {scP : semCallParams}
  {p : prog (pT := pT)}
  {ev : extra_val_t}
  {spec : HoareSpec}
.

Lemma hoare_fun_rec ii fn : hoare_f_rec p ev spec preF ii fn postF.
Proof. by move=> fs hpre /=; apply lutt_trigger. Qed.

Definition hoare_io_rec P c Q :=
  hoare_io (iE0 := invEvent_recCall spec) p ev P c Q.

Let hoare_io_fun_body_hyp_rec Pf fn Qf Qerr :=
  forall fs,
    Pf fn fs ->
    [/\ forall e, Qerr e -> rInvErr (estate0 fs) e
      & match get_fundef (p_funcs p) fn with
        | None => Qerr ErrType
        | Some fd =>
          [/\ sem_pre p  fn fs = ok tt
            , forall fr, Qf fn fs fr -> sem_post p fn fs.(fvals) fr = ok tt
            & exists (P : Pred_c) (Q : Pred_io estate estate),
              [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P Qerr
                , hoare_io_rec P fd.(f_body) Q
                , forall s s' e, Q s s' -> Qerr e -> rInvErr (estate0 fs) e
                & forall s,
                    P s -> rhoare (Q s) (finalize_funcall fd) (Qf fn fs) Qerr]]
        end].

Lemma hoare_io_fun_body Pf fn Qf Qerr :
  hoare_io_fun_body_hyp_rec Pf fn Qf Qerr ->
  hoare_f_body (iE0 := iE0) (iEr := iEr) p ev Pf fn Qf.
Proof.
  move=> hf; rewrite /hoare_f_body /isem_fun_body.
  apply khoare_ioP => fs hPf; have [herr {}hf] := hf _ hPf.
  apply khoare_read with (fun fd => get_fundef (p_funcs p) fn = Some fd).
  + rewrite /kget_fundef => ??.
    case: get_fundef hf => /= [fd | ] h; [apply lutt_Ret | apply lutt_Vis] => //.
    by rewrite preInv_Throw; apply herr.
  move=> fd hfd; move: hf; rewrite hfd => -[Pre Post [P] [Q] [hinit hbody hQerr hfin]].
  apply khoare_read with PredT.
  + move => ? ?; subst.
    rewrite /isem_pre Pre => //=.
    by apply lutt_Ret.
  move => _ _.
  apply khoare_read with P.
  + move=> _ ->; have := hinit _ hPf.
    case: initialize_funcall => [s | e] h; [apply lutt_Ret | apply lutt_Vis] => //.
    by rewrite preInv_Throw; apply herr.
    move => s1 hs1.
  eapply khoare_read.
  + move => s hpre'.
    have := hbody _ hs1. admit.
  move => s hQ.
  eapply khoare_read.
  + move => s' hpre'.
    apply: khoare_iresult hQerr.
    + move=> ? e _. exact: herr.
    exact: hfin hs1.
  move => s' hQf.
  apply khoare_read with PredT.
  + move => ? ?; subst.
    rewrite /isem_post Post => //=.
    by apply lutt_Ret.
  move => ????; subst.
  by apply lutt_Ret.
Admitted.

Lemma ihoare_io_fun Qerr fn ii :
  (forall fn, hoare_io_fun_body_hyp_rec preF fn postF Qerr) ->
  hoare_f_ii (sem_F := sem_fun_full) p ev preF ii fn postF.
Proof using.
move=> h fs hpre.
apply: (interp_mrec_lutt (DPEv := preD spec) (DPAns := postD spec)).
- move=> {hpre fn fs} A [{}ii fn fs] /= hpre.
  have := hoare_io_fun_body (h fn) hpre.
  (* wrong iE0 *)
Admitted.

(*
Lemma sem_fun_full_unfold ii fn fs :
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
*)

End PROOF.
End HOARE.

Section HOARE.

Context
  {wa : WithAssert}
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

Section PROOF.

Context
  {pT : progT}
  {scP : semCallParams}
  {p : prog (pT := pT)}
  {ev : extra_val_t}
.

#[local] Existing Instance trivial_invErr.
#[local] Existing Instance trivial_invEvent.
#[local] Existing Instance noassert.

#[local] Instance spec : HoareSpec :=
  {|
    preF_ := relT;
    postF_ := fun _ fs fs' => mem_equiv (fmem fs) (fmem fs');
  |}.

Notation ihoare_io_rec := (hoare_io_rec (p := p) (ev := ev)).

Let post s s' := mem_equiv (emem s) (emem s').
Let Pc c := ihoare_io_rec PredT c post.
Let Pi i := ihoare_io_rec PredT [::i] post.
Let Pi_r ir := forall ii, Pi (MkI ii ir).

Lemma write_lval_mem_equiv wdb gd x v s s' :
  write_lval wdb gd x v s = ok s' ->
  post s s'.
Proof. by move=> /[dup] /write_lval_validw ? /write_lval_stack_stable ?. Qed.

Lemma write_lvals_mem_equiv wdb gd xs vs s s' :
  write_lvals wdb gd s xs vs = ok s' ->
  post s s'.
Proof. by move=> /[dup] /write_lvals_validw ? /write_lvals_stack_stable ?. Qed.

Lemma isem_cmd_mem_equiv c : Pc c.
Proof using.
apply: (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => {c} //; subst Pc Pi Pi_r.
- by move=> s _; apply lutt_Ret.
- move=> i c /= /hoare_ioP hi hc; apply/hoare_ioP => s _.
  apply: (hoare_cons (R := post s)) => //; first exact: hi.
  move=> s' h; apply: lutt_weaken (hc s' I) => // r; exact: mem_equiv_trans h.
- move=> x tg ty e ii; apply/hoare_ioP => s _.
  apply: (hoare_assgn _ (Qerr := rInvErr s) (Rv := PredT) (Rtr := PredT)) => //.
  - exact: rhoare_true.
  - move=> ??; exact: rhoare_true.
  move=> v _ _ ->; case h: write_lval => [?|//].
  exact: write_lval_mem_equiv h.
- move=> xs tg o es ii; apply/hoare_ioP => s _.
  apply: (hoare_opn _ (Qerr := rInvErr s) (Rve := PredT) (Rvo := PredT)) => //.
  - exact: rhoare_true.
  - move=> ??; exact: rhoare_true.
  move=> v _ _ ->; case h: write_lvals => [?|//].
  exact: write_lvals_mem_equiv h.
- move=> xs o es ii; apply/hoare_ioP => s _.
  apply: (hoare_syscall ev ii
    (Rv := PredT)
    (Ro := fun fs => mem_equiv (emem s) (fmem fs))
    (Qerr := rInvErr s)) => //.
  - exact: rhoare_true.
  - move=> s' <-; rewrite /khoare => vs _.
    rewrite /fexec_syscall.
    apply: (lutt_bind (R := fun _ => True)).
    + rewrite /iresult /err_result /=.
      case: exec_syscall_arg => [len|e] /=.
      * by apply lutt_Ret.
      * apply lutt_Vis => /=.
        - by rewrite /preInv /= /subevent /= /resum /= /fromErr mid12.
        - move=> [].
    move=> t1 _.
    apply: (lutt_bind (R := fun _ => True)).
    + apply: lutt_trigger => //. admit.
    move=> [scs bytes] _.
    apply: (lutt_bind (R := fun scsmvs => mem_equiv (emem s') scsmvs.1.2)).
    + rewrite /iresult /err_result /mk_fstate /=.
      case he: exec_syscall_store => [[[scs' m'] vres]|e] /=.
      * by apply lutt_Ret; exact: exec_syscall_storeS he.
      * apply lutt_Vis => /=. admit.
      done.
    move=> [[scs' m'] vres] hRo.
    by apply lutt_Ret.
  - move=> fs hRo s0 ->.
    rewrite /upd_estate.
    case h: write_lvals => [s''|e] /=.
    + apply: mem_equiv_trans hRo _.
      exact: write_lvals_mem_equiv h.
    + done.
- move=> a ii; apply/hoare_ioP => s _.
  by apply: (hoare_assert ev ii (Qerr := rInvErr s)) => //.
- move=> e c1 c2 hc1 hc2 ii; apply/hoare_ioP => s _.
  apply: (hoare_if ii (Qerr := rInvErr s)) => //.
  - by move=> * /=; case: sem_cond.
  move=> b; case: b => /=.
  + move/hoare_ioP in hc1; exact: hc1 s I.
  + move/hoare_ioP in hc2; exact: hc2 s I.
- move=> v dir lo hi c hc ii; apply/hoare_ioP => s _.
  apply: (hoare_weaken1 (P2 := post s) (Q2 := post s)) => //.
  - by move=> s0 ->.
  apply: (hoare_for ii dir
    (P := post s) (Pi := post s) (Qerr := rInvErr s)) => //.
  - exact: rhoare_true.
  - move=> j s0 hs0; case h: write_var => [s1|e] /=.
    + by rewrite /post -(write_var_memP h).
    + done.
  - move=> s0 hs0; apply: lutt_weaken (hc s0 I) => // r;
      exact: mem_equiv_trans hs0.
- move=> a c e info c' hc hc' ii; apply/hoare_ioP => s _.
  apply: (hoare_weaken1 (P2 := post s) (Q2 := post s)) => //.
  - by move=> s0 ->.
  apply: (hoare_while (I := post s) (I' := post s) (Qerr := rInvErr s)) => //.
  - move=> s0 hs0; apply: lutt_weaken (hc s0 I) => // r;
      exact: mem_equiv_trans hs0.
  - exact: rhoare_true.
  - move=> s0 hs0; apply: lutt_weaken (hc' s0 I) => // r;
      exact: mem_equiv_trans hs0.
- move=> xs fn es ii; apply/hoare_ioP => s _.
  apply: hoare_call; only 5: exact: hoare_fun_rec.
Admitted.

Let MemEquivSpec fs : HoareSpec :=
  {|
    preF_ := fun _ => eq fs;
    postF_ := fun _ fs fs' => mem_equiv (fmem fs) (fmem fs');
  |}.

Lemma mem_equiv_equiv : Equivalence mem_equiv.
Proof.
split=> //; last exact: mem_equiv_trans.
by move=> ?? [? hv]; split=> [|???]; symmetry=> //; rewrite hv.
Qed.

Lemma sem_fun_mem_equiv fn ii :
  (forall s1 s2 m2 ef,
      init_state ef p.(p_extra) ev s1 = ok s2 ->
      mem_equiv (emem s2) m2 ->
      mem_equiv (emem s1) (finalize ef m2)) ->
  hoare_f_ii (sem_F := sem_fun_full) p ev
    relT
    ii fn
    (fun _ fs fs' => mem_equiv (fmem fs) (fmem fs')).
Proof using.
move=> h fs _.
apply: (ihoare_io_fun (spec := MemEquivSpec fs) (Qerr := PredT) _ _ erefl) =>
  {}fn _ <-; split=> //.
case hget: get_fundef => [fd|//]; split=> //.
exists
  (fun s => initialize_funcall p ev fd fs = ok s),
  (fun s s' => mem_equiv (emem s) (emem s'));
  split=> //.
- move=> _ <-; by case: initialize_funcall.
- apply:
    (khoare_io_weaken (P := PredT) (Q := post)) => //.
  - admit.
  - admit. (* isem_cmd_mem_equiv *)
move=> s hi s' hpost; case hf: finalize_funcall => [fs''|//].
move: hi hf; rewrite /initialize_funcall /finalize_funcall.
t_xrbindP=> _ _ s0 hi /write_vars_memP hw _ _ _ _ <- /= {fs''}.
apply: (h _ _ _ _ hi); rewrite hw; exact: hpost.
Admitted.

End PROOF.

#[local] Existing Instance trivial_invErr.
#[local] Existing Instance trivial_invEvent.
#[local] Existing Instance noassert.

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
