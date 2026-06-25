(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From ITree Require Import ITreeFacts.

Require Import xseq.
Require Export type expr gen_map warray_ sem_type sem_op_typed values varmap expr_facts low_memory syscall_sem psem_defs.
Require Export psem_core it_sems_core hoare_logic relational_logic.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Section WSW.
Context {wsw:WithSubWord}.

Section SEM.

Context
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (P : prog)
  (ev : extra_val_t).

Notation gd := (p_globs P).

Variables
  (Pc   : estate -> cmd -> estate -> Prop)
  (Pi_r : estate -> instr_r -> estate -> Prop).

Definition sem_Ind_assgn : Prop :=
  forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
    sem_pexpr true gd s1 e = ok v →
    truncate_val (eval_atype ty) v = ok v' →
    write_lval true gd x v' s1 = ok s2 →
    Pi_r s1 (Cassgn x tag ty e) s2.

Definition sem_Ind_opn : Prop :=
  forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
    sem_sopn gd o s1 xs es = ok s2 →
    Pi_r s1 (Copn xs t o es) s2.

Definition sem_Ind_syscall : Prop :=
  forall  s1 scs m s2 o xs es ves vs,
    sem_pexprs true gd s1 es = ok ves →
    exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
    write_lvals true gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
    Pi_r s1 (Csyscall xs o es) s2.

End SEM.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

Section ST_EQ.

Context
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams (wsw:= wsw) (pT := pT)}
  {dc: DirectCall}.

Lemma st_eq_refl d s : st_eq d s s.
Proof. by split. Qed.
Hint Resolve st_eq_refl : core.

Section PROG.

Context (p p': prog) (ev ev': extra_val_t).

Context (eq_globs: p_globs p = p_globs p').

Lemma st_eq_sem_pexpr wdb d e :
  wrequiv (st_eq d) ((sem_pexpr wdb (p_globs p))^~ e) ((sem_pexpr wdb (p_globs p'))^~ e) eq.
Proof.
  move=> s t v /st_relP [-> /=] hvm; rewrite eq_globs.
  rewrite -sem_pexpr_ext_eq //; eauto.
Qed.

Lemma st_eq_sem_pexprs wdb d es :
  wrequiv (st_eq d) ((sem_pexprs wdb (p_globs p))^~ es) ((sem_pexprs wdb (p_globs p'))^~ es) eq.
Proof.
  move=> s t v /st_relP [-> /=] hvm; rewrite eq_globs.
  rewrite -sem_pexprs_ext_eq //; eauto.
Qed.

Lemma st_eq_write_lvals wdb d x v d':
  wrequiv (st_eq d) (fun s => write_lvals wdb (p_globs p) s x v) (fun s => write_lvals wdb (p_globs p') s x v) (st_eq d').
Proof.
  rewrite eq_globs => s t s' /st_relP [-> /=] h1 h2.
  by have [vm2 h ->] := write_lvars_ext_eq h1 h2; eexists; eauto.
Qed.

Lemma st_eq_sem_eassert d e :
  wrequiv (st_eq d) ((sem_eassert (p_globs p))^~ e) ((sem_eassert (p_globs p'))^~ e) eq.
Proof.
  move=> s t v /st_relP [-> /=] hvm; rewrite eq_globs.
  rewrite -sem_eassert_ext_eq //; eauto.
Qed.

Lemma wdb_ok_eq wdb1 wdb2 : wdb_ok wdb1 wdb2 -> wdb1 = wdb2.
Proof. by case => -[-> ->]. Qed.

Lemma checker_st_eqP : Checker_eq p p' checker_st_eq.
Proof.
  constructor.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- <-; apply st_eq_sem_pexprs.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- <- vs; apply st_eq_write_lvals.
Qed.

Lemma checker_a_st_eqP : Checker_a_eq p p' checker_a_st_eq.
Proof. constructor; move=> > ->; apply st_eq_sem_eassert. Qed.
#[local] Hint Resolve checker_st_eqP checker_a_st_eqP : core.

Section FUN.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i := wequiv p p' ev ev' (st_eq tt) [::i] [::i] (st_eq tt).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c := wequiv p p' ev ev' (st_eq tt) c c (st_eq tt).

Lemma wequiv_st_eq c :
  (forall ii f, wequiv_f_ii p p' ev ev' (λ (_ _ : funname), eq) ii ii f f (λ (_ _ : funname) (_ _ : fstate), eq)) ->
  Pc c.
Proof.
  move=> hf; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}.
  + by apply wequiv_nil.
  + by move=> *; apply wequiv_cons with (st_eq tt).
  + by move=> >;apply wequiv_assgn_rel_eq with checker_st_eq tt.
  + by move=> >; apply wequiv_opn_rel_eq with checker_st_eq tt.
  + by move=> >; apply wequiv_syscall_rel_eq with checker_st_eq tt.
  + by move=> a ii; apply wequiv_assert_rel_eq with checker_a_st_eq.
  + by move=> > hc1 hc2 ii; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_eq with checker_st_eq tt tt.
  + by move=> > hc hc' ii; apply wequiv_while_rel_eq with checker_st_eq tt.
  by move=> ????; apply wequiv_call_rel_eq with checker_st_eq tt => //; apply hinit.
Qed.

End FUN.

Section ESEM.

Let Pi i :=
  forall s1 s2 vm1,
    esem_i p ev i s1 = ok s2 ->
    (evm s1 =1 vm1)%vm ->
    exists2 vm2, esem_i p' ev i (with_vm s1 vm1) = ok (with_vm s2 vm2) & evm s2 =1 vm2.

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c :=
  forall s1 s2 vm1,
    esem p ev c s1 = ok s2 ->
    (evm s1 =1 vm1)%vm ->
    exists2 vm2, esem p' ev c (with_vm s1 vm1) = ok (with_vm s2 vm2) & evm s2 =1 vm2.

Lemma esem_vm_eq s1 c s2 vm1:
  esem p ev c s1 = ok s2 ->
  (evm s1 =1 vm1)%vm ->
  exists2 vm2, esem p' ev c (with_vm s1 vm1) = ok (with_vm s2 vm2) & evm s2 =1 vm2.
Proof.
  move: s1 s2 vm1; apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => // {c}.
  + by move=> s1 s2 vm1 /= [<-] ?; exists vm1.
  + move=> i c hi hc s1 s2 vm1 /=; t_xrbindP.
    move=> s1' hsi hsc heq.
    by have [vm1' -> /=] := hi _ _ _ hsi heq; apply: hc hsc.
  + move=> x tg ty e ii s1 s2 vm1 /=; rewrite /sem_assgn -eq_globs; t_xrbindP.
    move=> v he v' htr hw heq.
    rewrite -(sem_pexpr_ext_eq true (p_globs p) _ heq) he /= htr /=.
    by have [vm2 ??] := write_lvar_ext_eq heq hw; exists vm2.
  + move=> xs t o es ii s1 s2 vm1 /=; rewrite /sem_sopn -eq_globs; t_xrbindP.
    move=> vs' vs hes hop hw heq.
    rewrite -(sem_pexprs_ext_eq true (p_globs p) _ heq) hes /= hop /=.
    by have [vm2 ??] := write_lvars_ext_eq heq hw; exists vm2.
  + move=> xs o es ii s1 s2 vm1 /=; rewrite /sem_syscall -eq_globs /upd_estate; t_xrbindP.
    move=> vs hes fs ho hw heq.
    rewrite -(sem_pexprs_ext_eq true (p_globs p) _ heq) hes /= ho /= /upd_estate.
    by have /(_ _ heq) [vm2 ??]:= write_lvars_ext_eq _ hw; exists vm2.
  + move=> e c1 c2 hc1 hc2 ii s1 s2 vm1 /=; rewrite /sem_cond -eq_globs; t_xrbindP.
    move=> b v he hb hc heq.
    rewrite -(sem_pexpr_ext_eq true (p_globs p) _ heq) he /= hb /= => {hb}.
    by case: b hc heq; [apply hc1 | apply hc2].
  move=>  i d lo hi c hc ii s1 s2 vm1 /=; rewrite /sem_bound -eq_globs; t_xrbindP.
  move=> ??? hlo htol ?? hhi htoh <- hf heq.
  rewrite -!(sem_pexpr_ext_eq true (p_globs p) _ heq) hlo hhi /= htol htoh /=.
  clear hlo hhi.
  elim: wrange s1 vm1 hf heq => [ | j js hrec] s1 vm1 /=.
  + by move=> [<-] ?; eexists; eauto.
  t_xrbindP.
  move=> s11 s12 hw hsc hf heq.
  have [vm2 /= heq1 -> /=] := [elaborate write_lvar_ext_eq (x:=Lvar i) (v:=Vint j) (gd:=[::]) heq hw].
  have [vm3 ] := hc _ _ _ hsc heq1.
  by rewrite /esem => -> /=; apply: hrec.
Qed.

End ESEM.

Section REC.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma wequiv_rec_st_eq c : wequiv_rec p p' ev ev' eq_spec (st_eq tt) c c (st_eq tt).
Proof.
  apply wequiv_st_eq.
  by move=> ii f s t <-; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

End PROG.

Section WIEQUIV_F.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma st_eq_finalize fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv (st_eq tt) (finalize_funcall fd) (finalize_funcall fd') eq.
Proof.
  rewrite /finalize_funcall => <- <- <- s t fs' [h1 h2 h3].
  t_xrbindP => vs.
  rewrite -!(sem_pexprs_get_var _ [::]).
  rewrite (sem_pexprs_ext_eq _ _ _ h3).
  case: s t h1 h2 h3 => scs mem vm1 [/= _ _ vm2] <- <- h3 -> /= ? -> <- /=.
  eexists; eauto.
Qed.

Lemma wiequiv_f_eq fn :
  wiequiv_f p p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
exists fd => // s1 ?; exists s1 => //; exists (st_eq tt), (st_eq tt).
split=> //; first exact/wequiv_rec_st_eq.
exact/st_eq_finalize.
Qed.

Lemma wiequiv_st_eq c : wiequiv p p ev ev (st_eq tt) c c (st_eq tt).
Proof. by apply wequiv_st_eq => // ii f ???; apply wiequiv_f_eq. Qed.

End WIEQUIV_F.

End ST_EQ.

Section IT_Sem_eqv.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Definition st_eq_on X := st_rel eq_on X.

Lemma read_es_st_eq_on gd wdb es X :
  Sv.Subset (read_es es) X ->
  wrequiv (st_eq_on X) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) eq.
Proof.
  move=> hsub s t v [???];rewrite (eq_on_sem_pexprs _ (s' := t)) //.
  + by move => ->; eauto.
  by apply: (eq_onI hsub).
Qed.

Lemma read_eassert_st_eq_on gd e X :
  Sv.Subset (read_eassert e) X ->
  wrequiv (st_eq_on X) ((sem_eassert gd)^~ e) ((sem_eassert gd)^~ e) eq.
Proof.
  move=> hsub s t b [???]. rewrite (eq_on_sem_eassert _ (s' := t)) //.
  + by move => ->; eauto.
  by apply: (eq_onI hsub).
Qed.

Lemma write_lvals_st_eq_on gd wdb xs vs X :
  Sv.Subset (read_rvs xs) X ->
  wrequiv
    (st_eq_on X)
    (λ s1 : estate, write_lvals wdb gd s1 xs vs) (λ s2 : estate, write_lvals wdb gd s2 xs vs)
    (st_eq_on (Sv.union (vrvs xs) X)).
Proof.
  move=> hsub s [?? vm] s' [/= <- <- hvm] hw.
  by have [vm' -> ? ] := write_lvals_eq_on hsub hw hvm; eexists; eauto.
Qed.

Definition check_es_st_eq_on (X:Sv.t) (es1 es2 : pexprs) (X':Sv.t) :=
  [/\ Sv.Subset X' X, es1 = es2 & Sv.Subset (read_es es1) X].

Definition check_lvals_st_eq_on (X:Sv.t) (xs1 xs2 : lvals) (X':Sv.t) :=
  [/\ Sv.Subset X' (Sv.union (vrvs xs1) X), xs1 = xs2 & Sv.Subset (read_rvs xs1) X].

Lemma check_esP_R_st_eq_on X es1 es2 X':
  check_es_st_eq_on X es1 es2 X' → ∀ s1 s2, st_rel eq_on X s1 s2 → st_rel eq_on X' s1 s2.
Proof. by move=> [h _ _]; apply st_rel_weaken => vm1 vm2; apply eq_onI. Qed.

Definition checker_st_eq_on : Checker_e (st_rel eq_on) :=
  {| check_es := check_es_st_eq_on;
     check_lvals := check_lvals_st_eq_on;
     check_esP_rel := check_esP_R_st_eq_on |}.

Definition check_a_st_eq_on (X:Sv.t) (e1 e2 : eassert) (X':Sv.t) :=
  [/\ Sv.Subset X' X, e1 = e2 & Sv.Subset (read_eassert e1) X].

Lemma check_aP_st_eq_on X e1 e2 X':
  check_a_st_eq_on X e1 e2 X' → ∀ s1 s2, st_rel eq_on X s1 s2 → st_rel eq_on X' s1 s2.
Proof. by move=> [h _ _]; apply st_rel_weaken => vm1 vm2; apply eq_onI. Qed.

Definition checker_a_st_eq_on : Checker_a (st_rel eq_on) :=
  {| check_a := check_a_st_eq_on
   ; check_aP_rel := check_aP_st_eq_on |}.

Definition st_uincl_on X := st_rel uincl_on X.

Lemma read_es_st_uincl_on gd wdb es X :
  Sv.Subset (read_es es) X ->
  wrequiv (st_uincl_on X) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) (values_uincl).
Proof.
  move=> hsub s t v /st_relP [-> /= h].
  by apply: sem_pexprs_uincl_on; apply: uincl_onI h.
Qed.

Lemma write_lvals_st_uincl_on gd wdb xs X vs1 vs2 :
  Sv.Subset (read_rvs xs) X ->
  values_uincl vs1 vs2 ->
  wrequiv
    (st_uincl_on X)
    (λ s1 : estate, write_lvals wdb gd s1 xs vs1) (λ s2 : estate, write_lvals wdb gd s2 xs vs2)
    (st_uincl_on (Sv.union (vrvs xs) X)).
Proof.
  move=> hsub hu s t s' /st_relP [-> /= h] hw.
  have [vm2 ? ->]:= write_lvals_uincl_on hsub hu hw h.
  by eexists; eauto.
Qed.

Lemma check_esP_R_st_uincl_on X es1 es2 X':
  check_es_st_eq_on X es1 es2 X' → ∀ s1 s2, st_rel uincl_on X s1 s2 → st_rel uincl_on X' s1 s2.
Proof. by move=> [h _ _]; apply st_rel_weaken => ??; apply uincl_onI. Qed.

Definition checker_st_uincl_on : Checker_e (st_rel uincl_on) :=
  {| check_es := check_es_st_eq_on;
     check_lvals := check_lvals_st_eq_on;
     check_esP_rel := check_esP_R_st_uincl_on |}.

Lemma st_eq_on_finalize fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv (st_eq_on (vars_l (f_res fd))) (finalize_funcall fd) (finalize_funcall fd') eq.
Proof.
  rewrite /finalize_funcall => <- <- <- /= s t fs [hscs hmem hvm].
  t_xrbindP => vs hget vs' htr <-.
  move: hget; rewrite -(sem_pexprs_get_var _ [::]) => hres.
  rewrite (eq_on_sem_pexprs (~~ direct_call) [::] hmem (eq_onI _ hvm)) in hres.
  2: by rewrite vars_l_read_es.
  rewrite sem_pexprs_get_var in hres.
  rewrite hres /= htr /= hscs hmem; eexists; eauto.
Qed.

Section PROG.

Context (p p':prog) (ev ev': extra_val_t).

Local Notation gd := (p_globs p).
Local Notation gd' := (p_globs p').

Context (eq_globs : gd = gd').

Lemma checker_st_eq_onP : Checker_eq p p' checker_st_eq_on.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [? <- ?]; apply read_es_st_eq_on.
  move=> wdb ? d xs1 xs2 d' /wdb_ok_eq <- [hsub <- ?] vs.
  apply wrequiv_weaken with (st_rel eq_on d) (st_rel eq_on (Sv.union (vrvs xs1) d)) => //.
  + by apply st_rel_weaken => ??; apply eq_onI.
  by apply write_lvals_st_eq_on.
Qed.

Lemma checker_a_st_eq_onP : Checker_a_eq p p' checker_a_st_eq_on.
Proof.
  constructor.
  move=> d es1 es2 d' [? <- ?]; rewrite eq_globs.
  by apply read_eassert_st_eq_on.
Qed.

#[local] Hint Resolve checker_st_eq_onP checker_a_st_eq_onP: core.

Lemma checker_st_uincl_onP : Checker_uincl p p' checker_st_uincl_on.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [? <- ?]; apply read_es_st_uincl_on.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- [hsub <- ?] vs1 vs2 hu.
  apply wrequiv_weaken with (st_rel uincl_on d) (st_rel uincl_on (Sv.union (vrvs xs1) d)) => //.
  + by apply st_rel_weaken => ??; apply uincl_onI.
  by apply: write_lvals_st_uincl_on hu.
Qed.

Section FUN.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i :=
  forall X, Sv.Subset (read_I i) X ->
    wequiv p p' ev ev' (st_eq_on X) [::i] [::i] (st_eq_on X).

Let Pi_r i :=
 forall ii X, Sv.Subset (read_i i) X ->
    wequiv p p' ev ev' (st_eq_on X) [::MkI ii i] [::MkI ii i] (st_eq_on X).

Let Pc c :=
  forall X, Sv.Subset (read_c c) X ->
  wequiv p p' ev ev' (st_eq_on X) c c (st_eq_on X).

Lemma it_read_cP_aux c X :
  (forall ii fn,
     wequiv_f_ii p p' ev ev' (λ (_ _ : funname), eq) ii ii fn fn (λ _ _  _ _, eq)) ->
  Sv.Subset (read_c c) X ->
  wequiv p p' ev ev' (st_eq_on X) c c (st_eq_on X).
Proof.
  move=> hfn; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c X}.
  + by move=> i ii hi X; apply hi.
  + by move=> ii X; apply wequiv_nil.
  + move=> i c hi hc X; rewrite read_c_cons => hsub.
    by apply wequiv_cons with (st_eq_on X); [apply hi | apply hc]; SvD.fsetdec.
  + move=> x tg ty e ii X. rewrite read_i_assgn => hsub.
    apply wequiv_assgn_rel_eq with checker_st_eq_on X => //=.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    split => //; first by SvD.fsetdec.
    by rewrite /read_rvs /= read_rvE; SvD.fsetdec.
  + move=> xs tg o es ii X. rewrite read_i_opn => hsub.
    by apply wequiv_opn_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + move=> xs sc es ii X. rewrite read_i_syscall => hsub.
    by apply wequiv_syscall_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + move=> a ii X; rewrite read_i_assert => hsub.
    by apply wequiv_assert_rel_eq with checker_a_st_eq_on => //; split.
  + move=> e c1 c2 hc1 hc2 ii X. rewrite read_i_if => hsub.
    apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc1; SvD.fsetdec.
    by apply hc2; SvD.fsetdec.
  + move=> i d lo hi c hc ii X; rewrite read_i_for => hsub.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; SvD.fsetdec.
    apply hc; SvD.fsetdec.
  + move=> a c e ii' c' hc hc' ii X. rewrite read_i_while => hsub.
    apply wequiv_while_rel_eq with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc; SvD.fsetdec.
    by apply hc'; SvD.fsetdec.
  + move=> xs fn es ii X; rewrite read_i_call => hsub.
  apply wequiv_call_rel_eq with checker_st_eq_on X => //.
  + by split => //; SvD.fsetdec.
  by split => //; SvD.fsetdec.
Qed.

End FUN.

Section REC.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_read_cP_rec X c :
  Sv.Subset (read_c c) X ->
  wequiv_rec p p' ev ev' eq_spec (st_eq_on X) c c (st_eq_on X).
Proof.
  apply it_read_cP_aux.
  by move=> ii f s t <-; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

End PROG.

Section REFL.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_read_cP X c :
  Sv.Subset (read_c c) X ->
  wiequiv p p ev ev (st_eq_on X) c c (st_eq_on X).
Proof.
  apply it_read_cP_aux => //= ii fn i1 i2 h.
  have /(_ i1 i2) := [elaborate wiequiv_f_eq p ev (fn:=fn)].
  by apply.
Qed.

End REFL.

End IT_Sem_eqv.

(* ---------------------------------------------------------------- *)
Section UNDEFINCL.

Context
  {dc:DirectCall}.

Lemma mapM2_id tyin vargs vargs' :
  mapM2 ErrType (λ (_ : ctype) (v : value), ok v) tyin vargs = ok vargs' ->
  vargs = vargs'.
Proof.
  elim: tyin vargs vargs' => /= [ | ty tyin hrec] [ | v vs] // >.
  + by move=> [].
  by t_xrbindP => > /hrec -> <-.
Qed.

Lemma dc_truncate_value_uincl t v1 v2 : dc_truncate_val t v1 = ok v2 → value_uincl v2 v1.
Proof.
  rewrite /dc_truncate_val; case: ifP => [_ [<-] // | _].
  apply truncate_value_uincl.
Qed.

Lemma mapM2_dc_truncate_value_uincl tyin vargs vargs' :
  mapM2 ErrType dc_truncate_val tyin vargs = ok vargs' → List.Forall2 value_uincl vargs' vargs.
Proof.
  rewrite /dc_truncate_val; case: direct_call; last by apply mapM2_truncate_value_uincl.
  by move=> /mapM2_id ->; apply List_Forall2_refl.
Qed.

Lemma mapM2_dc_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType dc_truncate_val tys vs1' = ok vs1 →
  List.Forall2 value_uincl vs1' vs2' →
  exists2 vs2 : seq value,
    mapM2 ErrType dc_truncate_val tys vs2' = ok vs2 & List.Forall2 value_uincl vs1 vs2.
Proof.
  rewrite /dc_truncate_val; case: direct_call; last by apply mapM2_truncate_val.
  move=> h1 h2; elim: h2 tys vs1 h1 => {vs1' vs2'} [ | v1 v2 vs1' vs2' hu hus hrec] [] //=.
  + by move=> ? [<-]; exists [::].
  t_xrbindP => _ tys ?? /hrec [vs2 -> hall] <- /=; eexists; eauto.
Qed.

End UNDEFINCL.

(* ---------------------------------------------------------------- *)
Section IT_UNDEFINCL.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Lemma read_es_st_uincl d gd wdb es :
  wrequiv (st_uincl d) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) (values_uincl).
Proof. by move=> s t vs /st_relP [/= -> h]; apply sem_pexprs_uincl. Qed.

Lemma write_lvals_st_uincl d d' gd wdb xs vs1 vs2 :
  values_uincl vs1 vs2 ->
  wrequiv
    (st_uincl d)
    (λ s1 : estate, write_lvals wdb gd s1 xs vs1) (λ s2 : estate, write_lvals wdb gd s2 xs vs2)
    (st_uincl d').
Proof.
  move=> hu s t s' /st_relP [/= -> h] hw.
  by have [vm' -> ?] := writes_uincl h hu hw; eexists; eauto.
Qed.

Section PROG.

Context (p p':prog) (ev ev': extra_val_t).

Local Notation gd := (p_globs p).
Local Notation gd' := (p_globs p').

Context (eq_globs : gd = gd').

Lemma checker_st_uinclP : Checker_uincl p p' checker_st_uincl.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- <-; apply read_es_st_uincl.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- <-; apply write_lvals_st_uincl.
Qed.
#[local] Hint Resolve checker_st_uinclP : core.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i := wequiv p p' ev ev' (st_uincl tt) [::i] [::i] (st_uincl tt).

Let Pi_r i :=
  forall ii, wequiv p p' ev ev' (st_uincl tt) [::MkI ii i] [::MkI ii i] (st_uincl tt).

Let Pc c :=
  wequiv p p' ev ev' (st_uincl tt) c c (st_uincl tt).

Lemma it_sem_uincl_aux c :
  (forall ii fn,
     wequiv_f_ii p p' ev ev' (λ (_ _ : funname), fs_uincl) ii ii fn fn (λ _ _  _ _, fs_uincl)) ->
  wequiv p p' ev ev' (st_uincl tt) c c (st_uincl tt).
Proof.
  move=> hfn; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}.
  + by move=> i ii hi X; apply hi.
  + by move=> ii X; apply wequiv_nil.
  + move=> i c hi hc.
    by apply wequiv_cons with (st_uincl tt).
  + by move=> x tg ty e ii; apply wequiv_assgn_rel_uincl with checker_st_uincl tt.
  + by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
  + by move=> xs sc es ii; apply wequiv_syscall_rel_uincl with checker_st_uincl tt.
  + by move=> a ii; apply wequiv_noassert.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
  + by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
  by move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt.
Qed.

End PROG.

Section REFL.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Definition uincl_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs_uincl fs1 fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fs_uincl fr1 fr2 |}.

Lemma eq_initialize p' fd fd' fs s:
  f_tyin fd = f_tyin fd' ->
  f_extra fd = f_extra fd' ->
  f_params fd = f_params fd' ->
  p_extra p = p_extra p' ->
  initialize_funcall p ev fd fs = ok s ->
  initialize_funcall p' ev fd' fs = ok s.
Proof. by rewrite /initialize_funcall => <- <- <- <-. Qed.

(* TODO: Can we generalize this to different semantic ? *)
Lemma fs_uincl_initialize p' fd fd' fs fs' s:
  f_tyin fd = f_tyin fd' ->
  f_extra fd = f_extra fd' ->
  f_params fd = f_params fd' ->
  p_extra p = p_extra p' ->
  fs_uincl fs fs' ->
  initialize_funcall p ev fd fs = ok s ->
  exists2 s', initialize_funcall p' ev fd' fs' = ok s' & st_uincl tt s s'.
Proof.
  move=> hty hex hpa hpex hfs; rewrite /initialize_funcall -hty -hex -hpa -hpex /estate0 /=.
  case: hfs => <- <- hu.
  t_xrbindP => vs htr s0 -> hw.
  have [vs' -> {}hu /=] := mapM2_dc_truncate_val htr hu.
  have [vm] := [elaborate write_vars_uincl (vm_uincl_refl (evm s0)) hu hw].
  by rewrite with_vm_same => -> ? /=; eexists; eauto.
Qed.

(* TODO: Can we generalize this to different semantic ? *)
Lemma fs_uincl_finalize fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv (st_uincl tt) (finalize_funcall fd) (finalize_funcall fd') fs_uincl.
Proof.
  rewrite /finalize_funcall => <- <- <- /= s t fs [<- <- hvm].
  t_xrbindP => vs hget vs' htr <-.
  have [vs1 -> hu /=] := get_var_is_uincl hvm hget.
  have [vs1' -> {}hu /=] := mapM2_dc_truncate_val htr hu.
  by eexists; eauto.
Qed.

Lemma fs_uincl_on_finalize fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv (st_uincl_on (vars_l (f_res fd))) (finalize_funcall fd) (finalize_funcall fd') fs_uincl.
Proof.
  rewrite /finalize_funcall => <- <- <- /= s t fs /st_relP [-> /= hvm].
  t_xrbindP => vs hget vs' htr <-.
  move: hget; rewrite -(sem_pexprs_get_var _ [::]) => hres.
  have [| vres1 + hu]:= sem_pexprs_uincl_on (uincl_onI _ hvm) hres.
  + by rewrite vars_l_read_es.
  rewrite sem_pexprs_get_var /= => -> /=.
  have [vs1' -> {}hu /=] := mapM2_dc_truncate_val htr hu.
  by eexists; eauto.
Qed.

Lemma it_sem_uincl_f fn :
  wiequiv_f p p ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
apply wequiv_fun_ind => {}fn _ fs1 fs2 [<-] hu fd ->.
exists fd => // s /(fs_uincl_initialize erefl erefl erefl erefl hu) [t] -> {}hu.
exists t => //; exists (st_uincl tt), (st_uincl tt); split=> //.
+ apply it_sem_uincl_aux => // ii fn' fs1' fs2' h; exact/wequiv_fun_rec.
exact/fs_uincl_finalize.
Qed.

Lemma it_sem_uincl c :
  wiequiv p p ev ev (st_uincl tt) c c (st_uincl tt).
Proof.
  by apply it_sem_uincl_aux => // ? fn ?? h; apply it_sem_uincl_f.
Qed.

End REFL.

Section REC.

Context (p p':prog) (ev ev': extra_val_t).

Context (eq_globs: p_globs p = p_globs p').

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_sem_uincl_rec c :
  wequiv_rec p p' ev ev' uincl_spec (st_uincl tt) c c (st_uincl tt).
Proof.
  apply it_sem_uincl_aux => //.
  by move=> ii f s t hu; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

Section EQ_CMD.

Section PROG.

Context (p p':prog) (ev ev': extra_val_t).

Context (eq_globs : p.(p_globs) = p'.(p_globs)).

Definition check_es_eq_cmd (_:unit) es1 es2 (_:unit) : Prop := all2 eq_expr es1 es2.
Definition check_lvals_eq_cmd (_:unit) lvs1 lvs2 (_:unit) : Prop := all2 eq_lval lvs1 lvs2.

Lemma check_esP_R_st_eq_cmd (d:unit) es1 es2 (d':unit) :
  check_es_eq_cmd d es1 es2 d' → ∀ s1 s2, st_rel (λ _ : unit, vm_uincl) d s1 s2 → st_rel (λ _ : unit, vm_uincl) d' s1 s2.
Proof. by move=> ?; apply st_rel_weaken. Qed.

Definition checker_eq_cmd : Checker_e (st_rel (λ _ : unit, vm_uincl)) :=
  {| check_es := check_es_eq_cmd;
     check_lvals := check_lvals_eq_cmd;
     check_esP_rel := check_esP_R_st_eq_cmd |}.

Lemma checker_eq_cmdP : Checker_uincl p p' checker_eq_cmd.
Proof.
  constructor; rewrite -eq_globs.
  + move=> wdb _ d es1 es2 d' /wdb_ok_eq <- hes s t vs1 /st_relP [-> /= huincl] hvs1.
    have [vs2 hvs2 hincl]:= sem_pexprs_uincl huincl hvs1.
    rewrite (eq_exprsP _ _ _ hes) in hvs2.
    by exists vs2.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- hxs vs1 vs2 hincl s t s' /st_relP [-> /= huincl] hs'.
  have [vm2 {}hs' {}huincl] := writes_uincl huincl hincl hs'.
  rewrite (eq_lvalsP _ _ _ _ hxs) in hs'.
  by exists (with_vm s' vm2).
Qed.
#[local] Hint Resolve checker_eq_cmdP : core.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i :=
  forall i', eq_instr i i' ->
  wequiv p p' ev ev' (st_uincl tt) [::i] [::i'] (st_uincl tt).

Let Pi_r i :=
  forall i', eq_instr_r i i' ->
  forall ii ii', wequiv p p' ev ev' (st_uincl tt) [::MkI ii i] [::MkI ii' i'] (st_uincl tt).

Let Pc c :=
  forall c', eq_cmd c c' ->
  wequiv p p' ev ev' (st_uincl tt) c c' (st_uincl tt).

Lemma it_eq_cmdP_aux c :
  (forall ii ii' fn,
     wequiv_f_ii p p' ev ev' (λ (_ _ : funname), fs_uincl) ii ii' fn fn (λ _ _  _ _, fs_uincl)) ->
  forall c', eq_cmd c c' ->
  wequiv p p' ev ev' (st_uincl tt) c c' (st_uincl tt).
Proof.
  move=> hfn; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => {c}.
  + by move=> i ii hi [??] /= ?; apply hi.
  + by move=> [|//] _; apply wequiv_nil.
  + move=> i c hi hc [//|i' c'] /= /andP [/hi{}hi /hc{}hc].
    by apply wequiv_cons with (st_uincl tt).
  + move=> x tg ty e [] //= x' tg' ty' e' /andP[] /andP[] /andP[] /eqP -> /eqP -> heq1 heq2 ??.
    apply wequiv_assgn_rel_uincl with checker_eq_cmd tt => //.
    + by rewrite /= /check_es_eq_cmd /= andbT.
    by rewrite /= /check_lvals_eq_cmd /= andbT.
  + move=> xs tg o es [] //= xs' tg' o' es' /andP[] /andP[] /andP[] heq1 /eqP -> /eqP -> heq2 ??.
    by apply wequiv_opn_rel_uincl with checker_eq_cmd tt.
  + move=> xs o es [] //= xs' o' es' /andP[] /andP[] heq1 /eqP -> heq2 ??.
    by apply wequiv_syscall_rel_uincl with checker_eq_cmd tt.
  + move=> [??] [] //= [??] /= /andP[] /eqP -> heq ??.
    by apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 [] //= e' c1' c2' /andP[] /andP[] heq /hc1{}hc1 /hc2{}hc2 ??.
    apply wequiv_if_rel_uincl with checker_eq_cmd tt tt tt => //.
    by rewrite /= /check_es_eq_cmd /= andbT.
  + move=> [??] dir lo hi c hc [] //= [??] [[dir' lo'] hi'] c'
      /andP[] /andP[] /andP[] /andP[] /eqP -> /eqP -> heq1 heq2 /hc{}hc ??.
    apply wequiv_for_rel_uincl with checker_eq_cmd tt tt => //.
    + by rewrite /= /check_es_eq_cmd /= heq1 heq2.
    by rewrite /= /check_lvals_eq_cmd /= eqxx.
  + move=> a c1 e info c2 hc1 hc2 [] //= a' c1' e' info' c2'
      /andP[] /andP[] /andP[] /eqP -> /hc1{}hc1 heq /hc2{}hc2 ??.
    apply wequiv_while_rel_uincl with checker_eq_cmd tt => //.
    by rewrite /= /check_es_eq_cmd /= andbT.
  move=> xs fn es [] //= xs' fn' es' /andP[] /andP[] heq1 /eqP -> heq2 ??.
  by apply wequiv_call_rel_uincl with checker_eq_cmd tt.
Qed.

End PROG.

Section REC.

Context (p p':prog) (ev ev': extra_val_t).

Context (eq_globs: p_globs p = p_globs p').

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_eq_cmdP_rec c c' :
  eq_cmd c c' ->
  wequiv_rec p p' ev ev' uincl_spec (st_uincl tt) c c' (st_uincl tt).
Proof.
  apply it_eq_cmdP_aux => //.
  by move=> ii ii' f s t hu; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

End EQ_CMD.

Context
  {pT1 : progT}
  {wsw1 : WithSubWord}
  {scP1 : semCallParams (wsw := wsw1) (pT := pT1)}
  {dc1 : DirectCall}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE12 : EventRels E0}
  {rE_trans : EventRels_trans rE12 rE12 rE12}
  {p1 : prog (pT := pT1)} {p2 : prog (pT := pT)}
  {ev1 : extra_val_t (progT := pT1)} {ev2 : extra_val_t (progT := pT)}
  {fn1 fn2 : funname}
.

Notation wiequiv_f :=
  (wiequiv_f
     (pT1 := pT1) (wsw1 := wsw1) (scP1 := scP1) (dc1 := dc1)
     (pT2 := pT) (wsw2 := wsw) (scP2 := sCP) (dc2 := dc)
     p1 p2 ev1 ev2).

Lemma it_sem_refl_EU_UU :
  wiequiv_f (rpreF (eS := eq_spec)) fn1 fn2 (rpostF (eS := uincl_spec)) ->
  wiequiv_f (rpreF (eS := uincl_spec)) fn1 fn2 (rpostF (eS := uincl_spec)).
Proof.
move=> h.
apply: (
  wiequiv_f_trans
    (rE23 := rE12)
    (p2 := p2) (ev2 := ev2) (fn2 := fn2)
    (rpreF12 := rpreF (eS := eq_spec))
    (rpreF23 := rpreF (eS := uincl_spec))
    (rpostF12 := rpostF (eS := uincl_spec))
    (rpostF23 := rpostF (eS := uincl_spec))
    _ _ h
).
- move=> s1 s2 [<- hincl]; by exists s1.
- move=> s1 s2 s3 s1' s3' [<- <-] [_ hincl] [s2' [?? hincl1'] [?? hincl2']].
  split; [congruence | congruence|].
  exact: Forall2_trans value_uincl_trans hincl1' hincl2'.
exact: it_sem_uincl_f.
Qed.

Lemma it_sem_refl_EE_UU :
  wiequiv_f (rpreF (eS := eq_spec)) fn1 fn2 (rpostF (eS := eq_spec)) ->
  wiequiv_f (rpreF (eS := uincl_spec)) fn1 fn2 (rpostF (eS := uincl_spec)).
Proof.
  move=> h; apply: it_sem_refl_EU_UU.
  apply: (
           wkequiv_io_weaken
             (P := rpreF (eS := eq_spec) fn1 fn2)
             (Q := rpostF (eS := eq_spec) fn1 fn2)
         ) => // ???? [_ <-] <-.
  exact: fs_uinclR.
Qed.

End IT_UNDEFINCL.

End WITH_PARAMS.

End WSW.

Notation pre_incl := (rpreF (eS := uincl_spec)).
Notation post_incl := (rpostF (eS := uincl_spec)).

Section REL_COMPOSE.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op : Type}
  {sip : SemInstrParams asm_op syscall_state}
  {fn1 fn2 fn3 : funname}
.

Lemma rpreF_trans_eq_eq_eq fs1 fs3 :
  pre_eq fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_eq fn1 fn2 fs1 fs2
    & pre_eq fn1 fn2 fs2 fs3.
Proof. move=> [<- <-]; by exists fs1. Qed.

Lemma rpreF_trans_eq_uincl_eq fs1 fs3 :
  pre_eq fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_incl fn1 fn2 fs1 fs2
    & pre_eq fn1 fn2 fs2 fs3.
Proof. move=> [<- <-]; exists fs1; split=> //; exact: fs_uinclR. Qed.

Lemma rpreF_trans_uincl_uincl_uincl fs1 fs3 :
  pre_incl fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_incl fn1 fn2 fs1 fs2
    & pre_incl fn1 fn2 fs2 fs3.
Proof. move=> [<- ?]; exists fs1; split=> //; exact: fs_uinclR. Qed.

Lemma rpostF_trans_eq_eq_eq_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_eq fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof. by move=> [<- h1] [<- <-] [] _ <-. Qed.

Lemma rpostF_trans_uincl_uincl_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_incl fn1 fn2 fs1 fs2 ->
  pre_incl fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- h1] [<- h2] [] r2 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_eq_eq_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- _] [<- <-] [] {}fs3 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_uincl_eq_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_incl fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- _] [<- <-] [] {}fs3 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_eq_uincl_eq_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_incl fn2 fn3 fs2 fs3 ->
  rcompose
    (post_eq fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof. by move=> [<- _] [<- [?? hvals1]] [] _ <- [?? hvals2]. Qed.

End REL_COMPOSE.

Section TRANS_UTILS.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op : Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT1 pT2 pT3 : progT}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {wsw1 wsw2 wsw3 : WithSubWord}
  {wa1 wa2 wa3 : WithAssert}
  {scP1 : semCallParams (wsw := wsw1) (pT := pT1)}
  {scP2 : semCallParams (wsw := wsw2) (pT := pT2)}
  {scP3 : semCallParams (wsw := wsw3) (pT := pT3)}
  {dc1 dc2 dc3 : DirectCall}
  {rE12 : EventRels E0} {rE23 : EventRels E0} {rE13 : EventRels E0}
  {sem_F1 : sem_Fun (sip := sip) (pT := pT1) E}
  {sem_F2 : sem_Fun (sip := sip) (pT := pT2) E}
  {sem_F3 : sem_Fun (sip := sip) (pT := pT3) E}
  {rE_trans : EventRels_trans rE12 rE23 rE13}
.

Notation prog1 := (prog (pT := pT1)).
Notation prog2 := (prog (pT := pT2)).
Notation prog3 := (prog (pT := pT3)).

Context
  {p1 : prog1} {p2 : prog2} {p3 : prog3}
  {ev1 : extra_val_t (progT := pT1)}
  {ev2 : extra_val_t (progT := pT2)}
  {ev3 : extra_val_t (progT := pT3)}
  {fn : funname}
.

Let wiequiv_f_trans' :=
  wiequiv_f_trans
    (wsw1 := wsw1) (wsw2 := wsw2) (wsw3 := wsw3)
    (wa1 := wa1) (wa2 := wa2) (wa3 := wa3)
    (scP1 := scP1) (scP2 := scP2) (scP3 := scP3)
    (dc1 := dc1) (dc2 := dc2) (dc3 := dc3)
    (p1 := p1) (p2 := p2) (p3 := p3)
    (ev1 := ev1) (ev2 := ev2) (ev3 := ev3)
    (fn1 := fn) (fn2 := fn) (fn3 := fn).

(* X -> wequiv eq uincl -> wequiv eq uincl *)
Let wiequiv_f_trans_X_EU {rpreF rpostF} :=
  wiequiv_f_trans'
    (rpreF12 := rpreF) (rpreF23 := pre_eq) (rpreF13 := pre_eq)
    (rpostF12 := rpostF) (rpostF23 := post_incl) (rpostF13 := post_incl).

(* wequiv eq eq -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_EE_EU :=
  wiequiv_f_trans_X_EU rpreF_trans_eq_eq_eq rpostF_trans_eq_eq_eq_uincl.

(* wequiv eq eq -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_EU_EU :=
  wiequiv_f_trans_X_EU rpreF_trans_eq_eq_eq rpostF_trans_eq_eq_uincl_uincl.

(* wequiv uincl uincl -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_UU_EU :=
  wiequiv_f_trans_X_EU
    rpreF_trans_eq_uincl_eq rpostF_trans_uincl_eq_uincl_uincl.

(* wequiv uincl uincl -> wequiv uincl uincl -> wequiv uincl uincl *)
Definition wiequiv_f_trans_UU_UU :=
  wiequiv_f_trans'
    rpreF_trans_uincl_uincl_uincl
    rpostF_trans_uincl_uincl_uincl_uincl.

End TRANS_UTILS.
