(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem allocation compiler_util.
Require Export inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section INLINE.

Context (inline_var: var -> bool).
Variable rename_fd : instr_info -> funname -> ufundef -> ufundef.

Lemma get_funP p ii f fd :
  get_fun p ii f = ok fd -> get_fundef p f = Some fd.
Proof. by rewrite /get_fun;case:get_fundef => // ? [->]. Qed.

Local Notation inline_i' := (inline_i inline_var rename_fd).
Local Notation inline_fd' := (inline_fd inline_var rename_fd).
Local Notation inline_prog' := (inline_prog inline_var rename_fd).

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
    apply (@cmd_rect Pr Pi Pc) => // {c}.
    + move=> i c Hi Hc X1 c' X2 /=.
      apply:rbindP => -[Xc cc] /Hc -> /=.
      by apply:rbindP => -[Xi ci] /Hi ->.
    + by move=> * ?.
    + by move=> * ?.
    + move=> e c1 c2 Hc1 Hc2 ii X1 c' X2 /=.
      apply: rbindP => -[Xc1 c1'] /Hc1 -> /=.
      by apply: rbindP => -[Xc2 c2'] /Hc2 -> /= [] <- <-.
    + move=> i dir lo hi c Hc ii X1 c0 X2 /=.
      by apply: rbindP => -[Xc c'] /Hc -> /=.
    + move=> a c e c' Hc Hc' ii X1 c0 X2 /=.
      apply: rbindP => -[Xc1 c1] /Hc -> /=.
      by apply: rbindP => -[Xc1' c1'] /Hc' -> /=.
    move=> i xs f es ii X1 c' X2 /=.
    case: i => //;apply: rbindP => fd /get_funP -/Incl.
    by rewrite /get_fun => ->.
  Qed.

  Lemma inline_incl fd fd' :
    inline_fd' p  fd = ok fd' ->
    inline_fd' p' fd = ok fd'.
  Proof.
    by case: fd => fi ftin fp fb ftout fr fe /=;apply: rbindP => -[??] /inline_c_incl -> [<-].
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
  apply: rbindP => p1 Hp1 /=.
  apply: rbindP => fd1';apply: add_finfoP => Hinl [] <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd';exists fd1;split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf1; rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd [? H]];exists fd;split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Lemma inline_progP' p p' f fd :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok p' ->
  get_fundef p f = Some fd ->
  exists fd', get_fundef p' f = Some fd' /\ inline_fd' p' fd = ok fd'.
Proof.
  elim: p p' => [ | [f1 fd1] p Hrec] p' //.
  rewrite /= => /andP [] Hf1 Huniq.
  apply: rbindP => p1 Hp1.
  apply: rbindP => fd1';apply: add_finfoP => Hinl [] <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd1;exists fd1';split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf1;rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd' [? H]];exists fd';split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
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

  Local Lemma Sif    : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii X2 Xc /=.
    apply: rbindP => Xc1 /Hc1 ?;apply:rbindP=> Xc2 /Hc2 ? [<-] /=.
    rewrite read_Ii read_i_if read_eE;SvD.fsetdec.
  Qed.

  Local Lemma Sfor   : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> i d lo hi c Hc ii X2 Xc;apply:rbindP => Xc' /Hc ? [<-]. Qed.

  Local Lemma Swhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii X2 Xc;apply:rbindP=> Xc' /Hc ?.
    by apply: rbindP=> Hc'' /Hc' ? [<-].
  Qed.

  Local Lemma Scall  : forall i xs f es, Pr (Ccall i xs f es).
  Proof.
    move=> i xs f es ii X2 Xc /=;case: i => [ | [<-] //].
    by apply:rbindP => fd _;apply: rbindP => ?? [<-].
  Qed.

  Lemma inline_c_subset c : Pc c.
  Proof.
    by apply (@cmd_rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i_subset i : Pr i.
  Proof.
    by apply (@instr_r_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i'_subset i : Pi i.
  Proof.
    by apply (@instr_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

End SUBSET.

Lemma assgn_tuple_Lvar (p:uprog) (ev:unit) ii (xs:seq var_i) flag tys es vs vs' s s' :
  let xs := map Lvar xs in
  disjoint (vrvs xs) (read_es es) ->
  sem_pexprs (p_globs p) s es = ok vs ->
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  write_lvals (p_globs p) s xs vs' = ok s' ->
  sem p ev s (assgn_tuple inline_var ii xs flag tys es) s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  elim: xs es tys vs vs' s s' => [ | x xs Hrec] [ | e es] [ | ty tys] [ | v vs] vs' s s' //=;
    try by move => _ _ /(@ok_inj _ _ _ _) <-.
  + by move=> _ _ [<-] [<-];constructor.
  + by move=> _; apply: rbindP => ??;apply:rbindP.
  + by move=> _ _;t_xrbindP => ? _ ? _ <-.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty.
  rewrite /=;t_xrbindP => ve Hse ves Hves ??;subst => v1 htr vs1 htrs <-.
  t_xrbindP => s1 Hw Hws.
  apply Eseq with s1.
  + by constructor;econstructor;eauto.
  apply: Hrec htrs Hws;first by SvD.fsetdec.
  apply:rbindP Hw => vm;apply: on_vuP.
  + move=> z ? <- [<-] /=.
    rewrite -Hves=> {Hse Hves};case:s => sm svm /=.
    apply read_es_eq_on with Sv.empty.
    by rewrite read_esE => y Hy;rewrite Fv.setP_neq //;apply/eqP;SvD.fsetdec.
  case:ifP => //= _ ? [<-] [<-] /=.
  rewrite -Hves=> {Hse Hves};case:s => sm svm /=.
  apply read_es_eq_on with Sv.empty.
  by rewrite read_esE => y Hy;rewrite Fv.setP_neq //;apply/eqP;SvD.fsetdec.
Qed.

Lemma assgn_tuple_Pvar (p:uprog) ev ii xs flag tys rxs vs vs' s s' :
  let es := map Plvar rxs in
  disjoint (vrvs xs) (read_es es) ->
  mapM (fun x : var_i => get_var (evm s) x) rxs = ok vs ->
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  write_lvals (p_globs p) s xs vs' = ok s' ->
  sem p ev s (assgn_tuple inline_var ii xs flag tys es) s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  have : evm s = evm s [\vrvs xs] by done.
  have : Sv.Subset (vrvs xs) (vrvs xs) by done.
  move: {1 3}s => s0;move: {2 3 4}(vrvs xs) => X.
  elim: xs rxs tys vs vs' s s' => [ | x xs Hrec] [ | rx rxs] [ | ty tys] [ | v vs] vs' s s' //=.
  + by move=> _ _ _ _ [<-] [<-];constructor.
  + by move=> _ _ _;apply: rbindP => ??;apply:rbindP.
  + by move=> _ _ _;t_xrbindP => ?????????? <-.
  + by move=> _ _ _ _ [<-].
  + by move=> _ _ _ _ [<-].
  rewrite vrvs_cons read_es_cons read_e_var /read_gvar /mk_lvar /= => Hsub Heqe Hempty.
  t_xrbindP => ve Hse vz Hses ?? v1 vs1 htr htrs ?; subst ve vz vs'.
  t_xrbindP => s1 Hw Hws; apply Eseq with s1.
  + constructor;econstructor;rewrite /=;eauto.
    rewrite /get_gvar /mk_lvar /=.
    have /get_var_eq_on <- //: evm s0 =[Sv.singleton rx] evm s.
    + by move=> y ?;apply: Heqe; SvD.fsetdec.
    by SvD.fsetdec.
  apply: Hrec Hses htrs Hws;[SvD.fsetdec| |SvD.fsetdec].
  by move=> y Hy;rewrite Heqe //;apply (vrvP Hw);SvD.fsetdec.
Qed.

Definition vm_uincl_on (X:Sv.t) (vm1 vm2 : vmap) :=
   forall x, Sv.In x X -> eval_uincl vm1.[x] vm2.[x].

Notation "vm1 '<=[' s ']' vm2" := (vm_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ]  '/'  vm2 ']'").

Lemma vm_uincl_onT vm2 X vm1 vm3 :
  vm1 <=[X] vm2 -> vm2 <=[X] vm3 -> vm1 <=[X] vm3.
Proof. move=> H1 H2 ? hin;apply: eval_uincl_trans (H1 _ hin) (H2 _ hin). Qed.

Lemma vm_uincl_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 <=[s2] vm2 -> vm1 <=[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vm_uincl_on_refl X vm : vm <=[X] vm.
Proof. done. Qed.

Global Instance vm_uincl_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl)
              vm_uincl_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vm_uincl_onI. Qed.

Global Instance vm_uincl_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vm_uincl_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vm_uincl_onI;rewrite Heq. Qed.

Lemma eq_on_uincl_on X vm1 vm2 : vm1 =[X] vm2 -> vm1 <=[X] vm2.
Proof. by move=> H ? /H ->. Qed.

Section PROOF.

  Variable p p' : uprog.
  Variable ev : unit.

  Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p].

  Hypothesis Hp : inline_prog' (p_funcs p) = ok (p_funcs p').

  Hypothesis eq_globs : p_globs p = p_globs p'.

  Let Pi_r s1 (i:instr_r) s2:=
    forall ii X1 X2 c', inline_i' (p_funcs p') (MkI ii i) X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
       sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi s1 (i:instr) s2:=
    forall X1 X2 c', inline_i' (p_funcs p') i X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pc s1 (c:cmd) s2:=
    forall X1 X2 c', inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X1 X2 c',
    inline_c (inline_i' (p_funcs p')) c X2 = ok (X1, c') ->
    Sv.Equal X1 X2 ->
    forall vm1, wf_vm vm1 -> evm s1 <=[X1] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 <=[X2] vm2 &
      sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfun m fn vargs m' vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists vres',
       sem_call p' ev m fn vargs' m' vres' /\
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s X1 X2 c' [<- <-] vm1 Hwf Hvm1;exists vm1;split=>//;constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc X1 X2 c0 /=;apply: rbindP => -[Xc c'] /Hc Hic.
    apply:rbindP => -[Xi i'] /Hi Hii [<- <-] vm1 /Hii H/H{H} [vm2 []].
    move=> /Hic H/H{H} [vm3 [Hwf3 Hvm3 Hsc']] ?.
    by exists vm3;split=> //;apply: sem_app Hsc'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi ??? /Hi. Qed.

  Lemma sem_pexpr_uincl_on gd s vm' vm m e v1 :
    vm <=[read_e_rec s e] vm' ->
    sem_pexpr gd {| emem := m; evm := vm |} e = ok v1 ->
    exists2 v2 : value,
      sem_pexpr gd {| emem := m; evm := vm' |} e = ok v2 & value_uincl v1 v2.
  Proof.
    move=> hsub.
    pose vm1 : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x (read_e_rec s e) then vm.[x] else vm'.[x]).
    rewrite (@read_e_eq_on _ s vm1) /with_vm /=; last first.
    + by move=> ? /Sv_memP; rewrite /vm1 Fv.get0 => ->.
    have hle: vm_uincl vm1 vm'.
    + by move=> ?;rewrite /vm1 Fv.get0;case:ifP => // /Sv_memP -/hsub.
    by apply: sem_pexpr_uincl. 
  Qed.

  Lemma sem_pexprs_uincl_on gd es s m vm vm' vs1 :
    vm <=[read_es_rec s es] vm'->
    sem_pexprs gd (Estate m vm) es = ok vs1 ->
    exists2 vs2,
       sem_pexprs gd (Estate m vm') es = ok vs2 &
       List.Forall2 value_uincl vs1 vs2.
  Proof.
    move=> hsub.
    pose vm1 : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x (read_es_rec s es) then vm.[x] else vm'.[x]).
    rewrite (@read_es_eq_on _ _ s _ vm1) /with_vm /=; last first.
    + by move=> ? /Sv_memP; rewrite /vm1 Fv.get0 => ->.
    have hle: vm_uincl vm1 vm'.
    + by move=> ?;rewrite /vm1 Fv.get0;case:ifP => // /Sv_memP -/hsub.
    by apply: sem_pexprs_uincl. 
  Qed.

  Lemma write_var_uincl_on X x v1 v2 s1 s2 vm1 :
    value_uincl v1 v2 ->
    write_var x v1 s1 = ok s2 ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.add x X]  vm2 &
      write_var x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_var_eq_on hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(write_var_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu]; eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Lemma write_lval_uincl_on gd X x v1 v2 s1 s2 vm1 :
    Sv.Subset (read_rv x) X ->
    value_uincl v1 v2 ->
    write_lval gd x v1 s1 = ok s2 ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.union (vrv x) X]  vm2 &
      write_lval gd x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> hsubset hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_lval_eq_on hsubset hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(write_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu];eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Lemma write_lvals_uincl_on gd X x v1 v2 s1 s2 vm1 :
    Sv.Subset (read_rvs x) X ->
    List.Forall2 value_uincl v1 v2 ->
    write_lvals gd s1 x v1 = ok s2 ->
    evm s1 <=[X]  vm1 ->
    exists2 vm2 : vmap,
      evm s2 <=[Sv.union (vrvs x) X]  vm2 &
      write_lvals gd (with_vm s1 vm1) x v2 = ok (with_vm s2 vm2).
  Proof.
    move=> hsubset hu hw hsub;pose vm1' : vmap :=
      Fv.empty (fun (x:var) => if Sv.mem x X then (evm s1).[x] else vm1.[x]).
    have heq_on :  evm s1 =[X] vm1'.
    + by move=> ? /Sv_memP;rewrite /vm1' Fv.get0 /= => ->.
    have [vm2' [heq_on' ]]:= write_lvals_eq_on hsubset hw heq_on.
    have: vm_uincl vm1' vm1.
    + by move=> ?;rewrite /vm1' Fv.get0 /=;case:ifP => // /Sv_memP -/hsub.
    move=> H /(writes_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu]; eexists; last reflexivity.
    by move=> ? hin;rewrite heq_on'.
  Qed.

  Notation gd := (p_globs p).

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e ve ve'.
    case: s1 s2 => sm1 svm1 [sm2 svm2] Hse hsub hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_assgn => Hwf Hvm.
    have /sem_pexpr_uincl_on -/(_ _ _ _ Hse): svm1 <=[read_e e] vm1.
    + by apply: vm_uincl_onI Hvm;SvD.fsetdec.
    move=> [v2 Hv2 Huv2].
    have [v2' hsub' huv2']:= truncate_value_uincl Huv2 hsub.
    have [ | vm2 /=Hvm2 Hw']:= write_lval_uincl_on _ huv2' hw Hvm; first by SvD.fsetdec.
    exists vm2;split.
    + by apply: wf_write_lval Hw'.
    + by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;econstructor; rewrite -?eq_globs;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    case: s1 s2 => sm1 svm1 [ sm2 svm2].
    apply: rbindP => ve;t_xrbindP => vs Hse Hso Hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_opn => Hwf Hvm.
    have /sem_pexprs_uincl_on  -/(_ _ _ _ Hse) : svm1 <=[read_es es] vm1.
    + by apply: vm_uincl_onI Hvm;SvD.fsetdec.
    move=> [v2 Hv2 Huv2].
    have [v2' [Hso' Huv2']]:= vuincl_exec_opn Huv2 Hso.
    have [ | vm2 /=Hvm2 Hw']:= write_lvals_uincl_on _ Huv2' Hw Hvm; first by SvD.fsetdec.
    exists vm2;split.
    + by apply: wf_write_lvals Hw'.
    + by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    by apply: sem_seq1;constructor;constructor;rewrite -eq_globs /sem_sopn Hv2 /= Hso'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] /Hc Hc1;apply: rbindP => -[Xc2 c2'] ? [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc1 vm1 _)=>//;first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_true => //.
    have /sem_pexpr_uincl_on : svm1 <=[read_e e] vm1 by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [ve' -> /value_uincl_bool1 -> /=].
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 =>  sm1 svm1 Hse _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] ?;apply: rbindP => -[Xc2 c2'] /Hc Hc2 [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc2 vm1 _)=>//;first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_false => //.
    have /sem_pexpr_uincl_on : svm1 <=[read_e e] vm1 by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [ve' -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s1 => sm1 svm1 Hsc Hc Hse Hsc' Hc' _ Hw ii X1 X2 cw Hi.
    move: (Hi) => /=;set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [Hwf2 Hvm2 Hsc1]].
    + apply: vm_uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    case : (Hc' _ _ _ Hc1' _ Hwf2) => [| vm3 [Hwf3 Hvm3 Hsc2]].
    + apply: vm_uincl_onI Hvm2; have /= -> := inline_c_subset Hc1'.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    have [vm4 [Hwf4 Hvm4 Hsw]]:= Hw _ _ _ _ Hi _ Hwf3 Hvm3.
    exists vm4;split => //;apply sem_seq1;constructor.
    case/semE: Hsw => si [] /sem_IE Hsw /semE ?; subst si.
    apply: (Ewhile_true Hsc1) Hsc2 Hsw.
    have /sem_pexpr_uincl_on : (evm s2) <=[read_e e] vm2.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    by rewrite -eq_globs;case: (s2) Hse => ?? he /(_ _ _ _ he) [? -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s1 s2 => sm1 svm1 [sm2 svm2] Hsc Hc Hse ii X1 X2 cw /=.
    set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [/=Hwf2 Hvm2 Hsc1]].
    + apply: vm_uincl_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    exists vm2;split=>//.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3;SvD.fsetdec.
    apply sem_seq1;constructor;apply Ewhile_false => //.
    have /sem_pexpr_uincl_on : svm2 <=[read_e e] vm2.
    + by apply: vm_uincl_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hse) [? -> /value_uincl_bool1 ->].
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => sm1 svm1 Hlo Hhi  _ Hf ii X1 X2 cf Hi.
    apply: rbindP Hi => -[Xc' c'] Hi [??] vm1 Hwf Hvm1;subst.
    have Hxc': Sv.Equal Xc' (Sv.union (read_i (Cfor i (d, lo, hi) c)) X2).
    + by have /= -> := inline_c_subset Hi;rewrite read_i_for;SvD.fsetdec.
    have [ /=| vm2 [Hwf2 Hvm2 Hsf]]:= Hf _ _ _ Hi Hxc' _ Hwf.
    + by apply: vm_uincl_onI Hvm1;rewrite Hxc'.
    exists vm2;split=>//;first by apply: vm_uincl_onI Hvm2;SvD.fsetdec.
    move: Hvm1;rewrite read_i_for => Hvm1.
    apply sem_seq1;constructor;eapply Efor;eauto=> /=.
    + have /sem_pexpr_uincl_on : svm1 <=[read_e lo] vm1 by apply: vm_uincl_onI Hvm1; SvD.fsetdec.     
      by rewrite -eq_globs => /(_ _ _ _ Hlo) [? -> /value_uincl_int1 ->].
    have /sem_pexpr_uincl_on: svm1 <=[read_e hi] vm1 by apply: vm_uincl_onI Hvm1; SvD.fsetdec.
    by rewrite -eq_globs => /(_ _ _ _ Hhi) [? -> /value_uincl_int1 ->].
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c X1 X2 c' Hc HX vm1 Hwf Hvm1;exists vm1;split=>//;first by rewrite -HX.
    constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor X1 X2 c' Hic HX vm1 Hwf Hvm1.
    have [vm1' Hvm1' Hw]:= write_var_uincl_on (value_uincl_refl _) Hwi Hvm1.
    have /(_ Hwf)Hwf' := wf_write_var _ Hw.
    have [|vm2 [] ]:= Hc _ _ _ Hic _ Hwf';first by apply: vm_uincl_onI Hvm1';SvD.fsetdec.
    rewrite -{1}HX => Hwf2 Hvm2 Hsc'.
    have [vm3 [?? Hsf']] := Hfor _ _ _ Hic HX _ Hwf2 Hvm2.
    by exists vm3;split=>//;apply: EForOne Hsc' Hsf'.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move => s1 m2 s2 ii xs fn args vargs vs.
    case:s1 => sm1 svm1 /= Hes Hsc Hfun Hw ii' X1 X2 c' /=;case:ii;last first.
    + move=> [<- <-] vm1 Hwf1 Hvm1.
      have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on _ Hes.
      + by apply: vm_uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
      have [vres' [Hscall Hvres]]:= Hfun _ Huargs.
      have [|vm2 /= Hvm2 Hxs] := write_lvals_uincl_on _ Hvres Hw Hvm1.
      + by rewrite read_i_call;SvD.fsetdec.
      exists vm2;split.
      + by apply: wf_write_lvals Hxs.
      + by apply: vm_uincl_onI Hvm2; rewrite read_i_call;SvD.fsetdec.
      by apply sem_seq1;constructor;eapply Ecall;eauto;rewrite -eq_globs.
    apply: rbindP => fd' /get_funP Hfd'.
    have [fd [Hfd Hinline]] := inline_progP uniq_funname Hp Hfd'.
    apply: rbindP => -[];apply:rbindP => -[];apply: add_infunP => Hcheckf /=.
    case:ifP => // Hdisj _ [] ??;subst X1 c' => vm1 Hwf1 Hvm1.
    have /(_ Sv.empty vm1) [|vargs' /= Hvargs' Huargs]:= sem_pexprs_uincl_on _ Hes.
    + by apply: vm_uincl_onI Hvm1;rewrite read_i_call;SvD.fsetdec.
    have [vres1 [Hscall Hvres]]:= Hfun _ Huargs.
    case/sem_callE: Hscall => f [].
    rewrite Hfd' => /(@Some_inj _ _ _) <- {f}.
    case => vargs0 [s0] [s1] [svm2] [vres] [hvs' [hs0 hs1] hsvm2 [hvres hvres1] hm2].
    have [vm0_ [vm1_ [vm2_ [vres2 [vres' [Htin [Hi Hwv] Hbody [Hvs Hall Htout] hm2']]]]]] :=
      CheckAllocRegU.alloc_funP_eq Hcheckf hvs' hs0 hs1 hsvm2 hvres hvres1 hm2.
    move: hs0 Hi hm2'; rewrite /init_state /finalize /=.
    move=> [?]; subst s0 => -[] ? _; subst vm0_ m2. 
    move=> {hvs' hs1 hsvm2 Hfd' Hfd Hcheckf Hsc Hinline}.
    move: Hdisj Hvm1;rewrite read_i_call.
    move: Htin Htout Hvs Hwv Hbody;set rfd := rename_fd _ _ => Htin Htout Hvs Hwv Hbody Hdisjoint Hvm1.
    rewrite (write_vars_lvals gd) in Hwv.
    have [||/= vm1' Wvm1' Uvm1']:= @writes_uincl gd _ _ vm1 _ vargs0 vargs0 _ _ Hwv.
    + by apply wf_vm_uincl. + by apply List_Forall2_refl.
    have Uvmi : vm_uincl (evm (with_vm s1 vm1_)) vm1' by done.
    have [/=vm3 [Hsem' Uvm3]]:= sem_uincl Uvmi Hbody.
    have [/=vs2' Hvs' Uvs']:= get_vars_uincl Uvm3 Hvs.
    have [vs' Htout' Uvs]:= mapM2_truncate_val Htout Uvs'.
    have Heqvm : svm1 <=[Sv.union (read_rvs xs) X2] vm3.
    + apply: (@vm_uincl_onT vm1);first by apply: vm_uincl_onI Hvm1;SvD.fsetdec.
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
    exists vm4;split.
    + apply: wf_write_lvals Hw';apply: (wf_sem Hsem') => -[xt xn].
      by have /(_ Hwf1 {|vtype := xt; vname := xn |}) /=:= wf_write_lvals _ Wvm1'.
    + by apply: vm_uincl_onI Hvm4;SvD.fsetdec.
    apply sem_app with (with_vm s1 vm1').
    + rewrite eq_globs !with_vm_idem in Hvargs', Wvm1'.
      apply: assgn_tuple_Lvar Hvargs' Htin Wvm1' => //.
      by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec /locals /locals_p vrvs_recE;SvD.fsetdec.
    apply: (sem_app Hsem').
    rewrite eq_globs in Hw' => {Hw}.
    case: (svm2) Hw' => emem2 evm2 Hw'.
    apply: assgn_tuple_Pvar Htout' Hw' => //;last first.
    move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec.
    by rewrite /locals /locals_p vrvs_recE read_cE write_c_recE;SvD.fsetdec.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s0 s1 svm2 vres vres' Hget Htin Hi Hw Hsem Hc Hres Htout Hfi.
    have [fd' [Hfd']{Hget}] := inline_progP' uniq_funname Hp Hget.
    case: fd Htin Hi Hw Hsem Hc Hres Htout Hfi => /= fi tin fx fc tout fxr fe 
             Htin Hi Hw Hsem Hc Hres Htout Hfi.
    apply: rbindP => -[X fc'] /Hc{Hc} Hc [] ?;subst fd'.
    move=> vargs1 Hall;move: Hw; rewrite (write_vars_lvals gd) => Hw.
    have heq : Sv.Equal (read_rvs [seq Lvar i | i <- fx]) Sv.empty.
    + elim: (fx);first by rewrite read_rvs_nil;SvD.fsetdec.
      by move=> ?? Hrec; rewrite /= read_rvs_cons /=;SvD.fsetdec.
    have [vargs1' htin' Hall'] := mapM2_truncate_val Htin Hall.
    have /(_ X) [|/= vm1]:= write_lvals_uincl_on _ Hall' Hw (vm_uincl_on_refl _).
    + by rewrite heq; SvD.fsetdec.
    move=> hsub Hvm1; case: (Hc vm1) => /=.
    + by apply: wf_write_lvals Hvm1; move: Hi => [<-];apply: wf_vmap0.
    + by apply: vm_uincl_onI hsub;SvD.fsetdec.
    move=> vm2' [hwf hsvm2 hsem].
    move: Hres; have /= <-:= @sem_pexprs_get_var gd svm2 => Hres.
    case: svm2 Hsem Hfi Hc hsvm2 hsem Hres => emem2 evm2 Hsem Hfi Hc hsvm2 hsem Hres.
    have [vres1 hvres1 Hall1]:= sem_pexprs_uincl_on hsvm2 Hres.
    have [vres1' hvres1' Hall1'] := mapM2_truncate_val Htout Hall1.
    exists vres1';split=> //;econstructor;eauto => /=.
    + by move: Hvm1; rewrite (write_vars_lvals gd) with_vm_same.
    by rewrite -(@sem_pexprs_get_var gd {| emem := emem2; evm := vm2' |}).
  Qed.

  Lemma inline_callP f mem mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p ev mem f va mem' vr ->
    exists vr',
      sem_call p' ev mem f va' mem' vr' /\  List.Forall2 value_uincl vr vr'.
  Proof.
    move=> Hall Hsem.
    apply (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem _ Hall).
  Qed.

End PROOF.

Lemma inline_call_errP p p' f ev mem mem' va va' vr:
  inline_prog_err inline_var rename_fd p = ok p' ->
  List.Forall2 value_uincl va va' ->
  sem_call p ev mem f va mem' vr ->
  exists vr',
      sem_call p' ev mem f va' mem' vr' /\  List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /inline_prog_err;case:ifP => //= Hu; t_xrbindP => fds Hi <-.
  by apply: (inline_callP (p':= {|p_globs := p_globs p; p_funcs:= fds|}) Hu Hi).
Qed.

End INLINE.

