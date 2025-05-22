(* ** Imports and settings *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem allocation_proof compiler_util.
Require Export inline.

Local Open Scope seq_scope.

Section INLINE.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t).

Lemma get_funP p f fd :
  get_fun p f = ok fd -> get_fundef p f = Some fd.
Proof. by rewrite /get_fun;case:get_fundef => // ? [->]. Qed.

Notation inline_i' := (inline_i rename_fd dead_vars_fd).
Notation inline_fd' := (inline_fd rename_fd dead_vars_fd).
Notation inline_prog' := (inline_prog rename_fd dead_vars_fd).

#[local] Existing Instance indirect_c.

Section INCL.

  Variable p p': ufun_decls.

  Hypothesis Incl : forall f fd,
    get_fundef p f = Some fd -> get_fundef p' f = Some fd.

  Let Pi i := forall X1 c' X2,
    inline_i' p  i X2 = ok (X1, c') ->
    inline_i' p' i X2 = ok (X1, c').

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=  forall X1 c' X2,
    inline_c (inline_i' p)  c X2 = ok (X1, c') ->
    inline_c (inline_i' p') c X2 = ok (X1, c').


  Lemma inline_c_incl c : Pc c.
  Proof.
    apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => // {c}.
    + move=> i c Hi Hc X1 c' X2 /=.
      by t_xrbindP => -[Xc cc] /Hc -> /= -[Xi ci] /Hi -> /= -> <-.
    1-4: by move=> * ?.
    + move=> e c1 c2 Hc1 Hc2 ii X1 c' X2 /=.
      by t_xrbindP => -[Xc1 c1'] /Hc1 -> /= -[Xc2 c2'] /Hc2 -> /= <- <-.
    + move=> i dir lo hi c Hc ii X1 c0 X2 /=.
      by t_xrbindP => -[Xc c'] /Hc -> /= <- <-.
    + move=> a c e ei c' Hc Hc' ii X1 c0 X2 /=.
      by t_xrbindP => -[Xc1 c1] /Hc -> /= -[Xc1' c1'] /Hc' -> /= <- <-.
    move=> xs f es ii X1 c' X2 /=.
    case: ii_is_inline => [|//].
    t_xrbindP=> fd /get_funP -/Incl.
    by rewrite /get_fun => -> h <- <- /=; rewrite h.
  Qed.

  Lemma inline_incl fd fd' :
    inline_fd' p  fd = ok fd' ->
    inline_fd' p' fd = ok fd'.
  Proof.
    by case: fd => fi ci ftin fp fb ftout fr fe /=;apply: rbindP => -[??] /inline_c_incl -> [<-].
  Qed.

End INCL.

Lemma inline_prog_fst p p' :
  inline_prog' p = ok p' ->
  [seq x.1 | x <- p] = [seq x.1 | x <- p'].
Proof.
  elim: p p' => [ ?[<-] | [f fd] p Hrec p'] //=.
  by apply: rbindP => ? /Hrec -> /=;apply:rbindP => ?? [] <-.
Qed.

Lemma inline_progP p p' f fd' :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok p' ->
  get_fundef p' f = Some fd' ->
  exists fd, get_fundef p f = Some fd /\ inline_fd' p' fd = ok fd'.
Proof.
  elim: p p' => [ | [f1 fd1] p Hrec] p' /=.
  + by move=> _ [<-].
  move=> /andP [] Hf1 Huniq.
  rewrite /inline_fd_cons; t_xrbindP => p1 Hp1 /= fd1' Hinl <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd';exists fd1;split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {}H.
    by move: Hf1; rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd [? H]];exists fd;split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Lemma inline_progP' p p' f fd :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok p' ->
  get_fundef p f = Some fd ->
  exists fd', get_fundef p' f = Some fd' /\ inline_fd' p' fd = ok fd'.
Proof.
  elim: p p' => [ | [f1 fd1] p Hrec] p' //.
  rewrite /= /inline_fd_cons => /andP [] Hf1 Huniq; t_xrbindP => p1 Hp1 fd1' Hinl <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd1;exists fd1';split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {}H.
    by move: Hf1;rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd' [? H]];exists fd';split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Section SUBSET.

  Variable p : ufun_decls.

  Let Pi i := forall X2 Xc,
    inline_i' p i X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_I i) X2).

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall X2 Xc,
      inline_c (inline_i' p) c X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_c c) X2).

  Local Lemma Smk    : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. done. Qed.

  Local Lemma Snil   : Pc [::].
  Proof. by move=> X2 Xc [<-]. Qed.

  Local Lemma Scons  : forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc X2 Xc /=.
    apply:rbindP=> Xc' /Hc ?;apply:rbindP => Xi /Hi ? [<-] /=.
    rewrite read_c_cons;SvD.fsetdec.
  Qed.

  Local Lemma Sasgn  : forall x tag t e, Pr (Cassgn x tag t e).
  Proof. by move=> ???? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sopn   : forall xs t o es, Pr (Copn xs t o es).
  Proof. by move=> ???? ii X2 Xc /= [<-]. Qed.

  Local Lemma Ssyscall   : forall xs o es, Pr (Csyscall xs o es).
  Proof. by move=> ??? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sassert : forall a, Pr (Cassert a).
  Proof. by move=> ? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sif    : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii X2 Xc /=.
    apply: rbindP => Xc1 /Hc1 ?;apply:rbindP=> Xc2 /Hc2 ? [<-] /=.
    rewrite read_Ii read_i_if read_eE;SvD.fsetdec.
  Qed.

  Local Lemma Sfor   : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> i d lo hi c Hc ii X2 Xc;apply:rbindP => Xc' /Hc ? [<-]. Qed.

  Local Lemma Swhile : forall a c e ei c', Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
  Proof.
    move=> a c e ei c' Hc Hc' ii X2 Xc;apply:rbindP=> Xc' /Hc ?.
    by apply: rbindP=> Hc'' /Hc' ? [<-].
  Qed.

  Local Lemma Scall : forall xs f es, Pr (Ccall xs f es).
  Proof.
    move=> xs f es ii X2 Xc /=.
    case: ii_is_inline => [|[<-] //].
    by apply:rbindP => fd _;apply: rbindP => ?? [<-].
  Qed.

  Lemma inline_c_subset c : Pc c.
  Proof.
    exact: (cmd_rect Smk Snil Scons Sasgn Sopn Ssyscall Sassert Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i_subset i : Pr i.
  Proof.
    exact:
      (instr_r_Rect Smk Snil Scons Sasgn Sopn Ssyscall Sassert Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i'_subset i : Pi i.
  Proof.
    exact:
      (instr_Rect Smk Snil Scons Sasgn Sopn Ssyscall Sassert Sif Sfor Swhile Scall).
  Qed.

End SUBSET.

Lemma assgn_tuple_Lvar (p:uprog) (ev:unit) ii (xs:seq var_i) flag tys es vs vs' s s' :
  let xs := map Lvar xs in
  disjoint (vrvs xs) (read_es es) ->
  sem_pexprs true (p_globs p) s es = ok vs ->
  mapM2 ErrType dc_truncate_val (map eval_atype tys) vs = ok vs' ->
  write_lvals true (p_globs p) s xs vs' = ok s' ->
  esem p ev (assgn_tuple ii xs flag tys es) s = ok s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  elim: xs es tys vs vs' s s' => [ | x xs Hrec] [ | e es] [ | ty tys] [ | v vs] vs' s s' //=;
    try by move => _ _ /ok_inj <-.
  + by t_xrbindP => _ > _ > _ <- <- > _ > _ <-.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty.
  rewrite /=;t_xrbindP => ve Hse ves Hves ??;subst => v1; rewrite /dc_truncate_val /= => htr vs1 htrs <-.
  t_xrbindP => s1 Hw Hws.
  rewrite /sem_assgn Hse /= htr /= Hw /=.
  apply: Hrec htrs Hws;first by SvD.fsetdec.
  symmetry; rewrite -Hves; apply eq_on_sem_pexprs.
  + by apply: write_var_memP Hw.
  apply: (eq_ex_disjoint_eq_on (vrvP_var Hw)); apply /disjointP; SvD.fsetdec.
Qed.

Lemma assgn_tuple_Pvar (p:uprog) ev ii xs flag tys rxs vs vs' s s' :
  let es := map Plvar rxs in
  disjoint (vrvs xs) (read_es es) ->
  get_var_is true (evm s) rxs = ok vs ->
  mapM2 ErrType dc_truncate_val (map eval_atype tys) vs = ok vs' ->
  write_lvals true (p_globs p) s xs vs' = ok s' ->
  esem p ev (assgn_tuple ii xs flag tys es) s = ok s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  have : evm s =[\vrvs xs] evm s  by done.
  have : Sv.Subset (vrvs xs) (vrvs xs) by done.
  move: {1 3}s => s0;move: {2 3 4}(vrvs xs) => X.
  elim: xs rxs tys vs vs' s s' => [ | x xs Hrec] [ | rx rxs] [ | ty tys] [ | v vs] vs' s s' //=.
  + by move=> _ _ _ _ [<-] [<-];constructor.
  + by move=> _ _ _;apply: rbindP => ??;apply:rbindP.
  + by move=> _ _ _;t_xrbindP => ?????????? <-.
  + by move=> _ _ _ _ [<-].
  + by move=> _ _ _ _ [<-].
  rewrite vrvs_cons read_es_cons read_e_var /read_gvar /mk_lvar /= => Hsub Heqe Hempty.
  t_xrbindP => ve Hse vz Hses ?? v1; rewrite /dc_truncate_val /= => htr vs1 htrs ?; subst ve vz vs'.
  t_xrbindP => s1 Hw Hws.
  rewrite /sem_assgn /= /get_gvar /mk_lvar /=.
  have /get_var_eq_on <- //: evm s0 =[Sv.singleton rx] evm s; last by SvD.fsetdec.
  + by move=> y ?;apply: Heqe; SvD.fsetdec.
  rewrite Hse /= htr /= Hw /=.
  apply: Hrec Hses htrs Hws;[SvD.fsetdec| |SvD.fsetdec].
  by move=> y Hy;rewrite Heqe //;apply (vrvP Hw);SvD.fsetdec.
Qed.

Section PROOF.

  Variable p p' : uprog.
  Variable ev : unit.

  Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p].

  Hypothesis Hp : inline_prog' (p_funcs p) = ok (p_funcs p').

  Hypothesis eq_globs : p_globs p = p_globs p'.

  Let Pi_r s1 (i:instr_r) s2:=
    forall ii X1 X2 c', inline_i' (p_funcs p') (MkI ii i) X2 = ok (X1, c') ->
    forall vm1, evm s1 <=[X1] vm1 ->
    exists2 vm2, evm s2 <=[X2] vm2 & sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pi s1 (i:instr) s2:=
    forall X1 X2 c', inline_i' (p_funcs p') i X2 = ok (X1, c') ->
    forall vm1, evm s1 <=[X1] vm1 ->
    exists2 vm2, evm s2 <=[X2] vm2 &
      sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pc s1 (c:cmd) s2:=
    forall X1 X2 c', inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c') ->
    forall vm1, evm s1 <=[X1] vm1 ->
    exists2 vm2, evm s2 <=[X2] vm2 &
      sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X1 X2 c',
    inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c') ->
    Sv.Equal X1 X2 ->
    forall vm1, evm s1 <=[X1] vm1 ->
    exists2 vm2, evm s2 <=[X2] vm2 &
      sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pfun scs m fn vargs scs' m' vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists2 vres',
       List.Forall2 value_uincl vres vres' &
       sem_call p' ev scs m fn vargs' scs' m' vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s X1 X2 c' [<- <-] vm1 Hvm1; exists vm1 => //; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc X1 X2 c0 /=;apply: rbindP => -[Xc c'] /Hc Hic.
    apply:rbindP => -[Xi i'] /Hi Hii [<- <-] vm1 /Hii [vm2 ].
    move=> /Hic [vm3 Hvm3 Hsc'] ?.
    by exists vm3 => //; apply: sem_app Hsc'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi ??? /Hi. Qed.

  Notation gd := (p_globs p).

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e ve ve'.
    case: s1 s2 => scs1 sm1 svm1 [scs2 sm2 svm2] Hse hsub hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_assgn => Hvm.
    have h : svm1 <=[read_e e] vm1 by apply: uincl_onI Hvm;SvD.fsetdec.
    have [v2 Hv2 Huv2 {h}] := sem_pexpr_uincl_on' h Hse.
    have [v2' hsub' huv2']:= value_uincl_truncate Huv2 hsub.
    have [ | vm2 /=Hvm2 Hw']:= write_lval_uincl_on _ huv2' hw Hvm; first by SvD.fsetdec.
    exists vm2; first by apply: uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;econstructor; rewrite -?eq_globs;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    case: s1 s2 => scs1 sm1 svm1 [ scs2 sm2 svm2].
    apply: rbindP => ve;t_xrbindP => vs Hse Hso Hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_opn => Hvm.
    have h : svm1 <=[read_es es] vm1 by apply: uincl_onI Hvm;SvD.fsetdec.
    have [v2 Hv2 Huv2 {h}] := sem_pexprs_uincl_on' h Hse.
    have [v2' Hso' Huv2' ]:= vuincl_exec_opn Huv2 Hso.
    have [ | vm2 /=Hvm2 Hw']:= write_lvals_uincl_on _ Huv2' Hw Hvm; first by SvD.fsetdec.
    exists vm2; first by apply: uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;constructor;rewrite -eq_globs /sem_sopn Hv2 /= Hso'.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move => s1 scs m s2 o xs es ves vs.
    case: s1 s2 => scs1 sm1 svm1 [ scs2 sm2 svm2] Hse Hso Hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_syscall => Hvm.
    have h : svm1 <=[read_es es] vm1 by apply: uincl_onI Hvm;SvD.fsetdec.
    have [v2 Hv2 Huv2 {h}] := sem_pexprs_uincl_on' h Hse.
    have [v2' Hso' Huv2']:= exec_syscallP Hso Huv2.
    have [ | vm2 /=Hvm2 Hw']:= write_lvals_uincl_on _ Huv2' Hw Hvm; first by SvD.fsetdec.
    exists vm2; first by apply: uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1; constructor; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] /Hc Hc1;apply: rbindP => -[Xc2 c2'] ? [<- <-] vm1.
    rewrite read_eE=> Hvm1.
    case: (Hc1 vm1 _)=>//;first by apply: uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 Hvm2 Hc1';exists vm2 => //.
    apply sem_seq1;constructor;apply Eif_true => //.
    have h : svm1 <=[read_e e] vm1 by apply: uincl_onI Hvm1;SvD.fsetdec.
    have {h} := sem_pexpr_uincl_on' h Hse.
    by rewrite -eq_globs => -[ve' -> /value_uinclE -> /=].
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] ?;apply: rbindP => -[Xc2 c2'] /Hc Hc2 [<- <-] vm1.
    rewrite read_eE=> Hvm1.
    case: (Hc2 vm1 _)=>//;first by apply: uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 Hvm2 Hc1'; exists vm2 => //.
    apply sem_seq1;constructor;apply Eif_false => //.
    have h : svm1 <=[read_e e] vm1 by apply: uincl_onI Hvm1;SvD.fsetdec.
    have {h} := sem_pexpr_uincl_on' h Hse.
    by rewrite -eq_globs => -[ve' -> /value_uinclE ->].
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e ei c'.
    case: s1 => scs1 sm1 svm1 Hsc Hc Hse Hsc' Hc' _ Hw ii X1 X2 cw Hi.
    move: (Hi) => /=;set X3 := Sv.union _ _; apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hvm1.
    case : (Hc _ _ _ Hc1 vm1) => [| vm2 Hvm2 Hsc1].
    + apply: uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    case : (Hc' _ _ _ Hc1' vm2) => [| vm3 Hvm3 Hsc2].
    + apply: uincl_onI Hvm2; have /= -> := inline_c_subset Hc1'.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    have [vm4 Hvm4 Hsw]:= Hw _ _ _ _ Hi _ Hvm3.
    exists vm4 => //;apply sem_seq1;constructor.
    case/semE: Hsw => si [] /sem_IE Hsw /semE ?; subst si.
    apply: (Ewhile_true Hsc1) Hsc2 Hsw.
    have h : (evm s2) <=[read_e e] vm2 by apply: uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    case: (s2) h Hse => ??? h Hse.
    have {h} := sem_pexpr_uincl_on' h Hse.
    by rewrite -eq_globs => -[? -> /value_uinclE ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 a c e ei c'.
    case: s1 s2 => scs1 sm1 svm1 [scs2 sm2 svm2] Hsc Hc Hse ii X1 X2 cw /=.
    set X3 := Sv.union _ _; apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hvm1.
    case : (Hc _ _ _ Hc1 vm1) => [| vm2 /= Hvm2 Hsc1].
    + apply: uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    exists vm2 => //.
    + by apply: uincl_onI Hvm2;rewrite /X3;SvD.fsetdec.
    apply sem_seq1;constructor;apply Ewhile_false => //.
    have h : svm2 <=[read_e e] vm2 by apply: uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    have {h} := sem_pexpr_uincl_on' h Hse.
    by rewrite -eq_globs => -[? -> /value_uinclE ->].
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => scs1 sm1 svm1 Hlo Hhi  _ Hf ii X1 X2 cf Hi.
    apply: rbindP Hi => -[Xc' c'] Hi [??] vm1 Hvm1;subst.
    have Hxc': Sv.Equal Xc' (Sv.union (read_i (Cfor i (d, lo, hi) c)) X2).
    + by have /= -> := inline_c_subset Hi;rewrite read_i_for;SvD.fsetdec.
    have [ /=| vm2 Hvm2 Hsf]:= Hf _ _ _ Hi Hxc' vm1.
    + by apply: uincl_onI Hvm1;rewrite Hxc'.
    exists vm2 => //;first by apply: uincl_onI Hvm2;SvD.fsetdec.
    move: Hvm1;rewrite read_i_for => Hvm1.
    apply sem_seq1;constructor;eapply Efor;eauto=> /=.
    + have h : svm1 <=[read_e lo] vm1 by apply: uincl_onI Hvm1; SvD.fsetdec.
      have := sem_pexpr_uincl_on' h Hlo.
      by rewrite -eq_globs => -[? -> /value_uinclE ->].
    have h: svm1 <=[read_e hi] vm1 by apply: uincl_onI Hvm1; SvD.fsetdec.
    have := sem_pexpr_uincl_on' h Hhi.
    by rewrite -eq_globs => -[? -> /value_uinclE ->].
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c X1 X2 c' Hc HX vm1 Hvm1;exists vm1 => //;first by rewrite -HX.
    constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor X1 X2 c' Hic HX vm1 Hvm1.
    have [vm1' Hw Hvm1']:= write_var_uincl_on (value_uincl_refl _) Hwi Hvm1.
    have [|vm2 ]:= Hc _ _ _ Hic vm1';first by apply: uincl_onI Hvm1';SvD.fsetdec.
    rewrite -{1}HX => Hvm2 Hsc'.
    have [vm3 ? Hsf'] := Hfor _ _ _ Hic HX _ Hvm2.
    by exists vm3 => //;apply: EForOne Hsc' Hsf'.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs.
    case: s1 => scs1 sm1 svm1 /= Hes Hsc Hfun Hw ii' X1 X2 c' /=.
    case: ii_is_inline; last first.
    + move=> [<- <-] vm1 Hvm1.
      have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on' _ Hes.
      + by apply: uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
      have [vres' Hvres Hscall]:= Hfun _ Huargs.
      have [|vm2 /= Hvm2 Hxs] := write_lvals_uincl_on _ Hvres Hw Hvm1.
      + by rewrite read_i_call;SvD.fsetdec.
      exists vm2.
      + by apply: uincl_onI Hvm2; rewrite read_i_call;SvD.fsetdec.
      by apply sem_seq1;constructor;eapply Ecall;eauto;rewrite -eq_globs.
    t_xrbindP => fd' /get_funP Hfd'.
    have [fd [Hfd Hinline]] := inline_progP uniq_funname Hp Hfd'.
    rewrite /check_rename; t_xrbindP => Hcheckf /=.
    case:ifP => // Hdisj _ ??;subst X1 c' => vm1 Hvm1.
    have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on' _ Hes.
    + by apply: uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
    have [vres1 Hvres Hscall]:= Hfun _ Huargs.
    case: (sem_callE Hscall) => f [].
    rewrite Hfd' => /Some_inj <- {f}.
    case => vargs0 [s0] [s1] [svm2] [vres] [hvs' [hs0 hs1] hsvm2 [hvres hvres1] [hscs2 hm2]].
    have [vm0_ [vm1_ [vm2_ [vres2 [vres' [Htin [Hi Hwv] Hbody [Hvs Hall Htout] [hscs2' hm2']]]]]]] :=
      alloc_fun_uprogP_eq Hcheckf hvs' hs0 hs1 hsvm2 hvres hvres1 hscs2 hm2.
    move: hs0 Hi hm2'; rewrite /init_state /finalize /=.
    move=> [?]; subst s0 => -[] ? _; subst vm0_ m2.
    move=> {hvs' hs1 hsvm2 Hfd' Hfd Hcheckf Hsc Hinline}.
    move: Hdisj Hvm1;rewrite read_i_call.
    move: Htin Htout Hvs Hwv Hbody;set rfd := rename_fd _ _ => Htin Htout Hvs Hwv Hbody Hdisjoint Hvm1.
    rewrite (write_vars_lvals _ gd) in Hwv.
    have [||/= vm1' Wvm1' Uvm1'] :=
      writes_uincl (vm1 := vm1) (v2 := vargs0) _ _ Hwv.
    + apply vm_uincl_init. + by apply List_Forall2_refl.
    have Uvmi : evm (with_vm s1 vm1_) <=1 vm1' by done.
    have [/=vm3 [Hsem' Uvm3]]:= sem_uincl Uvmi Hbody.
    have [/=vs2' Hvs' Uvs'] := get_var_is_uincl Uvm3 Hvs.
    have [vs' Htout' Uvs]:= mapM2_truncate_val Htout Uvs'.
    have Heqvm : svm1 <=[Sv.union (read_rvs xs) X2] vm3.
    + apply: uincl_onT;first by apply: uincl_onI Hvm1;SvD.fsetdec.
      apply: eq_on_uincl_on;apply eq_onT with vm1'.
      + apply: disjoint_eq_ons Wvm1'.
        move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec.
        by rewrite /locals_p vrvs_recE;SvD.fsetdec.
      move=> z Hz;apply (writeP Hsem').
      move: Hdisjoint;rewrite /disjoint /is_true /locals /locals_p !Sv.is_empty_spec.
      by rewrite vrvs_recE read_cE write_c_recE ;SvD.fsetdec.
    have HH: List.Forall2 value_uincl vs vs'.
    + by apply: (Forall2_trans value_uincl_trans Hvres); apply: (Forall2_trans value_uincl_trans Hall).
    have [|vm4 /= Hvm4 Hw']:= write_lvals_uincl_on _ HH Hw Heqvm;first by SvD.fsetdec.
    exists vm4.
    + by apply: uincl_onI Hvm4;SvD.fsetdec.
    apply sem_app with (with_vm s1 vm1').
    + rewrite eq_globs !with_vm_idem in Hvargs', Wvm1'.
      apply/esem_sem; apply: assgn_tuple_Lvar Hvargs' Htin Wvm1' => //.
      by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec /locals /locals_p vrvs_recE;SvD.fsetdec.
    apply: (sem_app Hsem').
    rewrite eq_globs in Hw' => {Hw}; subst scs2.
    case: (svm2) Hw' => escs2 emem2 evm2 Hw'.
    apply/esem_sem; apply: assgn_tuple_Pvar Htout' Hw' => //;last first.
    move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec.
    by rewrite /locals /locals_p vrvs_recE read_cE write_c_recE;SvD.fsetdec.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 svm2 vres vres' Hget Htin Hi Hw Hsem Hc Hres Htout Hscs Hfi.
    have [fd' [Hfd']{Hget}] := inline_progP' uniq_funname Hp Hget.
    case: fd Htin Hi Hw Hsem Hc Hres Htout Hfi => /= fi ci tin fx fc tout fxr fe
             Htin Hi Hw Hsem Hc Hres Htout Hfi.
    apply: rbindP => -[X fc'] /Hc{}Hc [] ?;subst fd'.
    move=> vargs1 Hall;move: Hw; rewrite (write_vars_lvals _ gd) => Hw.
    have heq : Sv.Equal (read_rvs [seq Lvar i | i <- fx]) Sv.empty.
    + elim: (fx);first by rewrite read_rvs_nil;SvD.fsetdec.
      by move=> ?? Hrec; rewrite /= read_rvs_cons /=;SvD.fsetdec.
    have [vargs1' htin' Hall'] := mapM2_truncate_val Htin Hall.
    have [|/=vm1] := write_lvals_uincl_on _ Hall' Hw (@uincl_on_refl _ _ X).
    + by rewrite heq; SvD.fsetdec.
    move=> hsub Hvm1; case: (Hc vm1) => /=.
    + by apply: uincl_onI hsub;SvD.fsetdec.
    move=> vm2' hsvm2 hsem.
    move: Hres; have /= <- := (sem_pexprs_get_var _ gd svm2) => Hres.
    case: svm2 Hsem Hscs Hfi Hc hsvm2 hsem Hres => escs2 emem2 evm2 Hsem Hscs Hfi Hc hsvm2 hsem Hres.
    have [vres1 hvres1 Hall1]:= sem_pexprs_uincl_on hsvm2 Hres.
    have [vres1' hvres1' Hall1'] := mapM2_truncate_val Htout Hall1.
    exists vres1' => //; econstructor; eauto => /=.
    + by move: Hvm1; rewrite (write_vars_lvals _ gd) with_vm_same.
    by rewrite
       -(sem_pexprs_get_var _
           gd
           {| escs := escs2; emem := emem2; evm := vm2'; |}).
  Qed.

  Lemma inline_callP f scs mem scs' mem' va va' vr :
    List.Forall2 value_uincl va va' ->
    sem_call p ev scs mem f va scs' mem' vr ->
    exists2 vr',
      List.Forall2 value_uincl vr vr' &
      sem_call p' ev scs mem f va' scs' mem' vr'.
  Proof.
    move=> Hall Hsem.
    exact:
      (sem_call_Ind
         Hskip
         Hcons
         HmkI
         Hassgn
         Hopn
         Hsyscall
         Hif_true
         Hif_false
         Hwhile_true
         Hwhile_false
         Hfor
         Hfor_nil
         Hfor_cons
         Hcall
         Hproc
         Hsem
         _
         Hall).
  Qed.

End PROOF.

Lemma inline_call_errP p p' f ev scs mem scs' mem' va va' vr:
  inline_prog_err rename_fd dead_vars_fd p = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p ev scs mem f va scs' mem' vr ->
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    sem_call p' ev scs mem f va' scs' mem' vr'.
Proof.
  rewrite /inline_prog_err;case:ifP => //= Hu.
  t_xrbindP => fds Hi <-.
  by apply: (inline_callP (p':= {|p_globs := p_globs p; p_funcs:= fds|}) Hu Hi).
Qed.

Section IT.

Section AUX.

(* Technical lemma: we don't have equality of the type signatures anymore,
   they are only convertible. We still manage to prove some equality, so luckily
   we don't have to mess with itrees.
   The lemma is put inside a different section, because we want to pick generic
   instances of the typeclasses involved. *)

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0} {sem_F : sem_Fun (pT:=progUnit) E}.

Lemma convertible_assgn_tuple tys1 tys2 :
  all2 convertible tys1 tys2 ->
  forall (p:uprog) ev ii rs tg es,
  isem_cmd_ p ev (assgn_tuple ii rs tg tys1 es) =
  isem_cmd_ p ev (assgn_tuple ii rs tg tys2 es).
Proof.
  elim: tys1 tys2 => [|ty1 tys1 ih1] [|ty2 tys2] //= /andP [hc1 hc2].
  move=> p ev ii [|r rs] tg [|e es] //=.
  rewrite (ih1 _ hc2).
  by rewrite /sem_assgn (convertible_eval_atype hc1).
Qed.

End AUX.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Section FD.

Context (p:uprog)
        {ev : extra_prog_t (progT := progUnit)}
        (pfuncs1: ufun_decls)
        (fn:funname) (fd fd':ufundef)
        (pfuncs2: ufun_decls).

Let pfuncs := pfuncs1 ++ (fn, fd) :: pfuncs2.

Hypothesis uniq_funname : uniq [seq x.1 | x <- pfuncs].

Hypothesis (inline_fd_ok : inline_fd rename_fd dead_vars_fd pfuncs2 fd = ok fd').

Let p1 : uprog :=
  {|p_funcs := pfuncs; p_globs := p_globs p; p_extra := p_extra p |}.

Let p2 : uprog :=
  {|p_funcs := pfuncs1 ++ (fn, fd') :: pfuncs2; p_globs := p_globs p; p_extra := p_extra p |}.

Definition do_inline caller iinfo (callee:funname) :=
  (caller == fn) && ii_is_inline iinfo.

Notation wequiv_rec :=
 (wequiv (rE0:=relEvent_recCall uincl_spec)
    (sem_F1 := sem_fun_inline do_inline fn) (sem_F2 := sem_fun_rec E) ).

Let Pi i :=
  forall X1 X2 c', inline_i' pfuncs2 i X2 = ok (X1, c') ->
  wequiv_rec p1 p2 ev ev (st_uincl_on X1) [::i] c' (st_uincl_on X2).
Let Pi_r i := forall ii, Pi (MkI ii i).
Let Pc c :=
  forall X1 X2 c', inline_c (inline_i' pfuncs2) c X2 = ok (X1, c') ->
  wequiv_rec p1 p2 ev ev (st_uincl_on X1) c c' (st_uincl_on X2).

Lemma checker_st_uincl_onP_ : Checker_uincl p1 p2 checker_st_uincl_on.
Proof. by apply checker_st_uincl_onP. Qed.
#[local] Hint Resolve checker_st_uincl_onP_ : core.

Lemma it_inline_fd_aux fn' :
  wiequiv_f p1 p2 ev ev (rpreF (eS:=uincl_spec)) fn' fn' (rpostF (eS:=uincl_spec)).
Proof.
  move=> fs1 fs2 hpre.
  rewrite (isem_call_inline p1 ev do_inline).
  move: fs1 fs2 hpre.
  apply wequiv_fun_ind_wa => hrec fn1 _ fs1 fs2 [<- hu] fd1 hfd1.
  have : if fn1 == fn then fd1 = fd /\ get_fundef (p_funcs p2) fn1 = Some fd' else get_fundef (p_funcs p2) fn1 = Some fd1.
  + move: hfd1; rewrite /p1 /p2 /get_fundef /= !assoc_cat.
    move: (uniq_funname); rewrite /pfuncs map_cat cat_uniq => /and3P [_ hhas _].
    case ha1 : assoc => [fd_ | ].
    + move=> [?]; subst fd_; case: eqP => // ?; subst fn1.
      by move: hhas => /=; rewrite (assoc_mem_dom' ha1).
    by rewrite /=; case: eqP => // ? [->].
  case: eqP; last first.
  (* First we show that for fn1 <> fn the semantic does not change *)
  + move=> hfn ->; exists fd1 => // _; split => //.
    move=> s1 hinit.
    have [s1' hinit' hus1] :=
      [elaborate fs_uincl_initialize (p:=p1) (p':=p2) (fs:= fs1) (fs':= fs2) erefl erefl erefl erefl hu hinit].
    exists s1' => //.
    exists (st_uincl ev), (st_uincl ev); split => //; last first.
    + by apply fs_uincl_finalize.
    move=> {fs1 fs2 hu s1 s1' hinit hinit' hus1} s t.
    have h: forall ii fn fs,
            Eqit.eutt eq (sem_fun (sem_Fun := sem_fun_inline do_inline fn1) p1 ev ii fn fs)
                         (sem_fun (sem_Fun := sem_fun_rec E) p1 ev ii fn fs).
    + move=> ii fn2 fs /=; rewrite /do_inline; case: eqP => //= ?; reflexivity.
    rewrite (isem_cmd_ext h) => {h}.
    by move: s t; apply it_sem_uincl_aux_wa => // ii fn2 ???; apply hrec.
  (* Second it works for fn1 *)
  move=> ? [? ->]; subst fn1 fd1; exists fd' => //.
  have : exists2 Xc,
          inline_c (inline_i' pfuncs2) (f_body fd) (read_es [seq Plvar i | i <- (f_res fd)]) = ok Xc &
          fd' = with_body fd Xc.2.
  + move: inline_fd_ok; rewrite /inline_fd; case: (fd) => >.
    by t_xrbindP => Xc h <-; exists Xc.
  move=> [[X1 c']].
  set X2 := read_es _.
  move=> hc' -> /= _; split => // s1 hinit.
  have [s1' hinit' hus1] :=
      [elaborate fs_uincl_initialize (p:=p1) (p':=p2) (fd:=fd) (fd':= with_body fd c')
                 (fs:= fs1) (fs':= fs2) erefl erefl erefl erefl hu hinit].
  exists s1' => //.
  exists (st_uincl_on X1), (st_uincl_on X2); split => //;
    first (by case hus1 => ?? h; split); last first.
  + have := [elaborate fs_uincl_on_finalize (fd:=fd) (fd':= with_body fd c') erefl erefl erefl].
    by apply wrequiv_weaken => //; apply st_rel_weaken => ??; rewrite /X2 vars_l_read_es.
  clear fs1 fs2 hu hfd1 hinit hinit' s1 s1' hus1 fn'.
  move: (f_body fd) X1 X2 c' hc'.

  apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => //; subst Pi Pi_r Pc => //=.
  + by move=> X1 X2 c' [] -> <-; apply wequiv_nil.
  + move=> i c hi hc X1 X2 c_; t_xrbindP.
    move=> [X c'] /hc{}hc [X' i'] /= /hi{}hi ? <-; subst X'.
    by rewrite -cat1s; apply wequiv_cat with (st_uincl_on X).
  + move=> x tg ty e ii X1 X2 _ [? <-].
    apply wequiv_assgn_rel_uincl with checker_st_uincl_on X1 => //=; subst X1; split => //.
    + by rewrite /read_es /= read_eE !read_writeE; SvD.fsetdec.
    + by rewrite !read_writeE; SvD.fsetdec.
    by rewrite /read_rvs !read_writeE /= read_rvE; SvD.fsetdec.
  + move=> xs tg o es ii X1 X2 _ [? <-].
    by apply wequiv_opn_rel_uincl with checker_st_uincl_on X1 => //=; subst X1; split => //;
      rewrite !read_writeE; SvD.fsetdec.
  + move=> xs o es ii X1 X2 _ [? <-].
    by apply wequiv_syscall_rel_uincl with checker_st_uincl_on X1 => //=; subst X1; split => //;
      rewrite !read_writeE; SvD.fsetdec.
  + by move=> ? ii ??? _; apply wequiv_noassert.
  + move=> e c1 c2 hc1 hc2 ii X1 X2 c_; t_xrbindP.
    move=> [X11 c1'] /hc1{}hc1 [X12 c2'] /hc2{}hc2 ? <-.
    apply wequiv_if_rel_uincl with checker_st_uincl_on X1 X2 X2 => //=; subst X1.
    + by split => //=; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + apply: wequiv_weaken hc1 => //=; apply st_rel_weaken => ??; apply uincl_onI.
      by rewrite read_eE; SvD.fsetdec.
    apply: wequiv_weaken hc2 => //=; apply st_rel_weaken => ??; apply uincl_onI.
    by rewrite read_eE; SvD.fsetdec.
  + move=> x dir lo hi c hc ii X1 X2 c_; t_xrbindP.
    move=> [X' c'] /[dup] /inline_c_subset /= hX' /hc{}hc ? <- /=.
    apply wequiv_weaken with (st_uincl_on X1) (st_uincl_on X1) => //.
    + by subst X1; apply st_rel_weaken => ??; apply uincl_onI; SvD.fsetdec.
    apply wequiv_for_rel_uincl with checker_st_uincl_on X1 X'; subst X1 => //=.
    + by split => //=; rewrite /read_es /= !read_eE !read_writeE; clear; SvD.fsetdec.
    by split => //; rewrite ?hX' !read_writeE /read_rvs /=; clear; SvD.fsetdec.
  + move=> al c1 e ii' c2 hc1 hc2 ii X1 X2 c_; t_xrbindP.
    move=> [Xc1 c1'] /[dup] /inline_c_subset /= hXc1 /hc1{}hc1.
    move=> [Xc2 c2']  /[dup] /inline_c_subset /= hXc2 /hc2{}hc2 ? <-.
    apply wequiv_weaken with (st_uincl_on X1) (st_uincl_on X1) => //.
    + by subst X1; apply st_rel_weaken => ??; apply uincl_onI; SvD.fsetdec.
    apply wequiv_while_rel_uincl with checker_st_uincl_on X1; subst X1 => //=.
    + by split => //; rewrite /read_es /= read_eE !read_writeE; clear; SvD.fsetdec.
    + apply: wequiv_weaken hc1 => //; apply st_rel_weaken => ??; apply uincl_onI.
      by rewrite hXc1 !read_writeE; clear; SvD.fsetdec.
    apply: wequiv_weaken hc2 => //; apply st_rel_weaken => ??; apply uincl_onI.
    by rewrite hXc2 !read_writeE; clear; SvD.fsetdec.
  move=> xs f es ii X1 X2 c_.
  case: ifP => hinline; last first.
  + move=> [? <-].
    apply wequiv_call_rel_uincl with checker_st_uincl_on X1; subst X1 => //=.
    + by split => //; rewrite !read_writeE; clear; SvD.fsetdec.
    + by split => //; rewrite !read_writeE; clear; SvD.fsetdec.
    move=> i1 i2 h; rewrite /= /do_inline eqxx hinline /=.
    by apply (hrec ii ii f f i1 i2).
  rewrite /check_rename.
  t_xrbindP => ffd /get_funP hffd.
  case: ifP => //; set ffd' := rename_fd ii f ffd.
  move=> hdisj hrename _ ? <-.
  move=> s t hpre /=.
  rewrite /do_inline eqxx hinline /=.
  rewrite ITree.Eq.Eqit.bind_ret_r /isem_fun_rec /isem_fun_body /isem_pexprs.
  case hes: sem_pexprs => [vs | ] /=; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l /isem_pre /sem_pre /isem_post /sem_post /=.
  rewrite ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind /kget_fundef.
  have -> /= : get_fundef pfuncs f = Some ffd.
  + move: uniq_funname; rewrite /get_fundef /pfuncs map_cat cat_uniq assoc_cat => /and3P [_ /= hhas /andP [hnin _]].
    case ha1 : assoc => [fd_ | ].
    + move/orP: hhas; elim; right; apply /hasP; exists f.
      + by apply: assoc_mem_dom' hffd.
      by apply: assoc_mem_dom' ha1.
    case: eqP => // ?; subst f.
    by move: hnin; rewrite (assoc_mem_dom' hffd).
  rewrite !ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind.
  case hinit : initialize_funcall => [s1 /= | ?]; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_bind.
  move: hinit; rewrite /initialize_funcall /=; t_xrbindP => vs' htr hws.
  rewrite isem_cmd_cat.
  move: hrename; rewrite /= /check_f_extra_u; t_xrbindP.
  move=> /and3P [] _ htyin htyout r1 hextra hparams r2 hc r3 hres _.
  have /(_ X1 es es X1 _ _ _ _ hpre hes) [|] := checker_st_uincl_onP_.(ucheck_esP) wdb_ok_true.
  + by subst X1; split => //; rewrite !read_writeE; clear; SvD.fsetdec.
  move=> vst hes' huvs.
  have [vst' htr' huvs'] := mapM2_dc_truncate_val htr huvs.
  have heqa_empty: eq_alloc M.empty (evm (estate0 (mk_fstate vs s))) (evm t).
  + by split => * //; rewrite Vm.initP.
  rewrite (write_vars_lvals _ (p_globs p1)) in hws.
  have [vm2 hws' heqa] := [elaborate check_lvalsP hparams heqa_empty huvs' hws].
  have heqt: (with_vm (estate0 (mk_fstate vs s)) (evm t)) = t.
  + by move: hpre => /st_relP [-> /=].
  rewrite heqt in hws'.
  have hdisje : disjoint (vrvs [seq Lvar i | i <- f_params ffd']) (read_es es).
  + apply /disjointP => z hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p !read_writeE vrvs_recE; move: hz; clear; SvD.fsetdec.
  have /(esem_i_bodyP (sem_F := sem_fun_rec E)) h := assgn_tuple_Lvar ev (ii_with_location ii) AT_rename hdisje hes' htr' hws'.
  rewrite -(convertible_assgn_tuple htyin) h.
  clear h => /=.
  rewrite ITree.Eq.Eqit.bind_ret_l isem_cmd_cat.
  have := [elaborate it_alloc_cP (p1:=p1) (p2:=p2) erefl hrec hc].
  move=> /wequiv_write2 -/(_ (with_vm s1 vm2)) h.
  apply xrutt_facts.xrutt_bind with
    (fun s2 s3 : estate => evm (with_vm s1 vm2) =[\write_c (f_body ffd')] evm s3 /\ st_eq_alloc r2 s2 s3).
  + by apply h.
  move=> s' t' [heqex {}heqa].
  rewrite ITree.Eq.Eqit.bind_bind.
  case hfinal : finalize_funcall => [fr /= | ?]; last first.
  + rewrite ITree.Eq.Eqit.bind_vis.
    apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite ITree.Eq.Eqit.bind_ret_l.
  rewrite ITree.Eq.Eqit.bind_bind !ITree.Eq.Eqit.bind_ret_l. 
  case hupd : upd_estate => [s1' /= | ?]; last first.
  + apply xrutt.xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  move: hfinal hupd.
  rewrite /finalize_funcall /upd_estate; t_xrbindP.
  move=> rvs hget rvs' {}htr <- {fr} /= {}hws.
  move/st_relP : (heqa) => [heqt' {}heqa'].
  have [_ /(_ rvs)]:= [elaborate check_esP (p1:=p1) (p2:=p2) erefl true hres heqa'].
  rewrite !sem_pexprs_get_var => /(_ hget) [rvst [hget' hu]].
  have [rvst' {}htr' {}hu] := mapM2_dc_truncate_val htr hu.
  have /(_ X1 xs xs X1 _ _ _ hu _ t' _ _ hws) [||]:= checker_st_uincl_onP_.(ucheck_lvalsP) wdb_ok_true.
  + split => //; first by clear;SvD.fsetdec.
    by subst X1; rewrite !read_writeE; clear; SvD.fsetdec.
  + subst X1; rewrite heqt'; split => //= z hz.
    rewrite -heqex; last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      by move: hz; clear; SvD.fsetdec.
    rewrite -(vrvsP hws'); last first.
    + move/disjointP: hdisj => /(_ z).
      rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
      by move: hz; clear; SvD.fsetdec.
    by case: hpre => _ _; apply.
  move=> t1' hws1 hpost.
  have hdisjr : disjoint (vrvs xs) (read_es [seq Plvar i | i <- f_res ffd']).
  + apply/disjointP => z; rewrite vars_l_read_es => hz.
    move/disjointP: hdisj => /(_ z).
    rewrite /locals_p vrvs_recE read_cE write_c_recE vars_l_read_es.
    by move: hz; clear; SvD.fsetdec.
  have := assgn_tuple_Pvar _ (ii_with_location ii) AT_rename hdisjr hget' htr'.
  rewrite -heqt' => /(_ p2 ev t1' hws1) /(esem_i_bodyP (sem_F := sem_fun_rec E)).
  rewrite (convertible_assgn_tuple htyout) => -> /=.
  apply xrutt.xrutt_Ret.
  by apply: st_rel_weaken hpost; subst X1 => ??; apply: uincl_onI; SvD.fsetdec.
Qed.

End FD.

Context
  {p : uprog}
  {ev : extra_prog_t (progT := progUnit)}
  {rE_trans : EventRels_trans rE rE rE}
.

Lemma inline_fd_consP (pfuncs1 pfuncs0 pfuncs2 pfuncs: ufun_decls) :
  foldr (inline_fd_cons  rename_fd dead_vars_fd) (ok pfuncs2) pfuncs1 = ok pfuncs ->
  let p1 := {|p_funcs := pfuncs0 ++ pfuncs1 ++ pfuncs2; p_globs := p_globs p; p_extra := p_extra p |} in
  let p2 := {|p_funcs := pfuncs0 ++ pfuncs; p_globs := p_globs p; p_extra := p_extra p |} in
  uniq [seq x.1 | x <- p_funcs p1] ->
  uniq [seq x.1 | x <- p_funcs p2] /\
  ((forall fn, wiequiv_f p p1 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec))) ->
   (forall fn, wiequiv_f p p2 ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)))).
Proof.
  elim: pfuncs1 pfuncs0 pfuncs2 pfuncs => /= [ | [fn1 fd1] pfuncs1 hrec] pfuncs0 pfuncs2 pfuncs.
  + by move=> [->].
  rewrite {1}/inline_fd_cons; t_xrbindP.
  move=> pfuncs' hpfuncs' /= fd1' hinline <- huniq.
  have := hrec (rcons pfuncs0 (fn1, fd1)) _ _ hpfuncs'.
  rewrite -cats1 -catA /= => /(_ huniq) [huniq'] {}hrec; split.
  + by move: huniq'; rewrite !map_cat /= -catA.
  move=> /hrec{}hrec fn.
  rewrite -catA /= in huniq'.
  have /(_ fn) := it_inline_fd_aux p (ev := ev) huniq' hinline.
  have := hrec fn; rewrite -catA /=.
  apply wiequiv_f_trans => //.
  + move=> fs1 fs2 [_ ?]; exists fs1 => //; split => //.
    by split => //; apply List_Forall2_refl.
  move=> _ _ _ fr1 fr3 _ _ [fr2].
  rewrite /fs_uincl /fs_rel => -[-> -> h1] [-> -> h2]; split => //.
  apply: Forall2_trans h1 h2; apply value_uincl_trans.
Qed.

Lemma it_inline_call_errP p' fn :
  inline_prog_err rename_fd dead_vars_fd p = ok p' ->
  wiequiv_f p p' ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  rewrite /inline_prog_err; case: ifP => //; t_xrbindP => huniq pfuncs h <-.
  have /(_ [::]) /= := inline_fd_consP h.
  rewrite cats0 => /(_ huniq) [_ ]; apply => fn'; rewrite (surj_prog p).
  by apply it_sem_uincl_f_wa.
Qed.

End IT.

End INLINE.
