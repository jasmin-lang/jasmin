From mathcomp Require Import ssreflect ssrfun ssrbool.

Require Import
  expr
  low_memory
  lowering
  psem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ESTATE_EQ_EXCEPT.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

(* State equality up to a set of variables. *)
Definition estate_eq_except ys s1 s2 :=
  [/\ s1.(escs) = s2.(escs), s1.(emem) = s2.(emem) & s1.(evm) =[\ ys] s2.(evm)].

(* FIXME syscall : why it is needed to redeclare it here *)
(* note that in utils, it is CMorphisms.Proper, here it is Morpisms.Proper *)
#[global]
Instance and3_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. apply and3_iff_morphism. Qed.
(* END FIXME syscall *)

Lemma eeq_excR xs s :
  estate_eq_except xs s s.
Proof. done. Qed.

Lemma eeq_excS xs s0 s1 :
  estate_eq_except xs s0 s1
  -> estate_eq_except xs s1 s0.
Proof. by rewrite /estate_eq_except => -[-> -> ->]. Qed.

Lemma eeq_excT xs s0 s1 s2 :
  estate_eq_except xs s0 s1
  -> estate_eq_except xs s1 s2
  -> estate_eq_except xs s0 s2.
Proof. by rewrite /estate_eq_except => -[-> -> ->]. Qed.

Lemma eeq_exc_disjoint xs ys s0 s1 :
  disjoint xs ys
  -> estate_eq_except ys s0 s1
  -> [/\ escs s0 = escs s1, emem s0 = emem s1 & evm s0 =[ xs ] evm s1].
Proof.
  move=> /Sv.is_empty_spec hdisj [-> -> hvm].
  split=> // x hxxs.
  apply: hvm.
  SvD.fsetdec.
Qed.

Lemma eeq_exc_sem_pexprs wdb gd xs es v s0 s1 :
  disjoint (read_es es) xs
  -> estate_eq_except xs s1 s0
  -> sem_pexprs wdb gd s0 es = ok v
  -> sem_pexprs wdb gd s1 es = ok v.
Proof.
  move=> hdisj heq.
  have [hscs hmem hvm] := eeq_exc_disjoint hdisj heq.
  rewrite (read_es_eq_on wdb gd hvm).
  rewrite /with_vm.
  rewrite hscs hmem.
  by rewrite -(surj_estate s0).
Qed.

Lemma eeq_exc_sem_pexpr wdb gd xs e v s0 s1 :
  disjoint (read_e e) xs
  -> estate_eq_except xs s1 s0
  -> sem_pexpr wdb gd s0 e = ok v
  -> sem_pexpr wdb gd s1 e = ok v.
Proof.
  move=> hdisj heq hsem.

  have hdisj' : disjoint (read_es [:: e ]) xs.
  - done.

  have hsem' : sem_pexprs wdb gd s0 [:: e ] = ok [:: v ].
  - by rewrite /= hsem.

  have := eeq_exc_sem_pexprs hdisj' heq hsem'.
  rewrite /=.
  by t_xrbindP => ? ? <-.
Qed.

Lemma eeq_exc_write_lvals wdb gd xs s0 s1 s0' ls vs :
  disjoint (vars_lvals ls) xs
  -> estate_eq_except xs s0' s0
  -> write_lvals wdb gd s0 ls vs = ok s1
  -> exists2 s1',
       write_lvals wdb gd s0' ls vs = ok s1' & estate_eq_except xs s1' s1.
Proof.
  move=> hdisj.
  move: s0 s0' => [scs0 mem0 vm0] [scs0' mem0' vm0'].
  move=> [/= hscs hmem hvm] hwrite.
  subst scs0 mem0.

  have hsub : Sv.Subset (read_rvs ls) (Sv.diff (read_rvs ls) xs).
  - rewrite /vars_lvals in hdisj.
    have [hdisj' _] := disjoint_union hdisj.
    exact: (disjoint_subset_diff hdisj').
  clear hdisj.

  have hvm' : vm0 =[Sv.diff (read_rvs ls) xs] vm0'.
  - move=> x hx. apply: eq_exS. apply: hvm. SvD.fsetdec.

  have [vm1' hwrite' hvm1'] := write_lvals_eq_on hsub hwrite hvm'.
  clear hsub hvm'.

  eexists; first exact: hwrite'.
  split=> //= x hx.
  case hxvrv : (Sv.mem x (vrvs ls)).
  - move: hxvrv => /Sv_memP hxvrv.
    rewrite hvm1'; first done.
    SvD.fsetdec.
  - move: hxvrv => /Sv_memP hxvrv.
    rewrite -(vrvsP hwrite' hxvrv) {hwrite'}.
    rewrite -(vrvsP hwrite hxvrv) {hwrite}.
    exact: hvm.
Qed.

Lemma eeq_exc_write_lval wdb gd xs s0 s1 s0' l v :
  disjoint (vars_lval l) xs
  -> estate_eq_except xs s0' s0
  -> write_lval wdb gd l v s0 = ok s1
  -> exists2 s1',
       write_lval wdb gd l v s0' = ok s1' & estate_eq_except xs s1' s1.
Proof.
  move=> hdisj heq hwrite.

  have hdisj' : disjoint (vars_lvals [:: l ]) xs.
  - done.

  have hwrite' : write_lvals wdb gd s0 [:: l ] [:: v ] = ok s1.
  - by rewrite /= hwrite.

  have [s1' hwrite1 heq1] := eeq_exc_write_lvals hdisj' heq hwrite'.

  eexists; last exact: heq1.
  move: hwrite1.
  rewrite /=.
  by t_xrbindP => ? ? <-.
Qed.

Lemma eeq_exc_get_gvar wdb gd s0 s1 (x : gvar) vs :
  ~~ Sv.mem (gv x) vs
  -> estate_eq_except vs s0 s1
  -> get_gvar wdb gd (evm s0) x = get_gvar wdb gd (evm s1) x.
Proof.
  move=> /Sv_memP hx [hscs hmem hvm].
  rewrite /get_gvar /=.
  case: is_lvar; last done.
  rewrite /get_var /=.
  by rewrite (hvm _ hx).
Qed.

End ESTATE_EQ_EXCEPT.


Section DISJ_FVARS.

Context
  {pT : progT}
  {asmop : Type}
  {asm_op : asmOp asmop}
  (all_fresh_vars : seq Ident.ident)
  (fvars : Sv.t).

Notation disj_fvars := (disj_fvars fvars).
Notation fvars_correct := (fvars_correct all_fresh_vars fvars).

Context
  (p : prog)
  (fv_correct : fvars_correct (p_funcs p)).

Lemma fvars_fresh : disj_fvars (vars_p (p_funcs p)).
Proof. by move: fv_correct => /andP []. Qed.

Lemma disj_fvars_read_e_Papp2 op e0 e1 :
  disj_fvars (read_e (Papp2 op e0 e1))
  -> disj_fvars (read_e e0) /\ disj_fvars (read_e e1).
Proof.
  rewrite /read_e /=.
  move=> /(disjoint_equal_l (read_eE _ _)).
  by move=> /disjoint_union [h0 h1].
Qed.

Lemma disj_fvars_read_e_Pif ty c e0 e1 :
  disj_fvars (read_e (Pif ty c e0 e1))
  -> [/\ disj_fvars (read_e c)
       , disj_fvars (read_e e0)
       & disj_fvars (read_e e1)
     ].
Proof.
  rewrite /read_e /=.
  move=> /(disjoint_equal_l (read_eE _ _)).
  move=> /disjoint_union [] hc.
  move=> /(disjoint_equal_l (read_eE _ _)).
  by move=> /disjoint_union [he0 he1].
Qed.

Lemma disj_fvars_vars_c_cons i c :
  disj_fvars (vars_c (i :: c))
  -> disj_fvars (vars_I i) /\ disj_fvars (vars_c c).
Proof.
  rewrite /disj_fvars. rewrite vars_c_cons. exact: disjoint_union.
Qed.

Lemma disj_fvars_vars_I_Cassgn ii lv tag ty e :
  disj_fvars (vars_I (MkI ii (Cassgn lv tag ty e)))
  -> disj_fvars (vars_lval lv) /\ disj_fvars (read_e e).
Proof.
  move=> /(disjoint_equal_l (vars_I_assgn ii lv tag ty e)).
  by move=> /disjoint_union.
Qed.

Lemma disj_fvars_vars_I_Copn ii lvs tag op es :
  disj_fvars (vars_I (MkI ii (Copn lvs tag op es)))
  -> disj_fvars (vars_lvals lvs) /\ disj_fvars (read_es es).
Proof.
  move=> /(disjoint_equal_l (vars_I_opn ii lvs tag op es)).
  by move=> /disjoint_union.
Qed.

Lemma disj_fvars_vars_I_Cif ii e c0 c1 :
  disj_fvars (vars_I (MkI ii (Cif e c0 c1)))
  -> [/\ disj_fvars (read_e e)
       , disj_fvars (vars_c c0)
       & disj_fvars (vars_c c1)
     ].
Proof.
  move=> /(disjoint_equal_l (vars_I_if ii e c0 c1)).
  by move=> /disjoint_union [] h0 /disjoint_union [h1 h2].
Qed.

Lemma disj_fvars_vars_I_Cwhile ii al c0 e c1 :
  disj_fvars (vars_I (MkI ii (Cwhile al c0 e c1)))
  -> [/\ disj_fvars (vars_c c0)
       , disj_fvars (read_e e)
       & disj_fvars (vars_c c1)
     ].
Proof.
  move=> /(disjoint_equal_l (vars_I_while ii al c0 e c1)).
  by move=> /disjoint_union [] h0 /disjoint_union [h1 h2].
Qed.

Lemma disj_fvars_vars_I_Cfor ii i d lo hi c :
  disj_fvars (vars_I (MkI ii (Cfor i (d, lo, hi) c)))
  -> [/\ disj_fvars (Sv.add i (vars_c c))
       , disj_fvars (read_e lo)
       & disj_fvars (read_e hi)
     ].
Proof.
  move=> /(disjoint_equal_l (vars_I_for ii i d lo hi c)).
  move=> /disjoint_union [] h /disjoint_union [h0 h1].
  split=> // {h0 h1}.
  apply: disjoint_equal_l _ h.
  apply: SvP.MP.equal_sym.
  rewrite SvP.MP.union_sym.
  exact: SvP.MP.add_union_singleton.
Qed.

Lemma disj_fvars_vars_I_Ccall ii lvs fn args :
  disj_fvars (vars_I (MkI ii (Ccall lvs fn args)))
  -> disj_fvars (vars_lvals lvs) /\ disj_fvars (read_es args).
Proof.
  move=> /(disjoint_equal_l (vars_I_call ii lvs fn args)).
  by move=> /disjoint_union.
Qed.

Lemma disj_fvars_get_fundef fn fd :
  get_fundef (p_funcs p) fn = Some fd
  -> [/\ disj_fvars (vars_l (f_params fd))
       , disj_fvars (vars_l (f_res fd))
       & disj_fvars (vars_c (f_body fd))
     ].
Proof.
  move=> hget.
  have := disjoint_w (vars_pP hget) fvars_fresh.
  by move=> /disjoint_union [] ? /disjoint_union [].
Qed.

Lemma disj_fvars_Cfor_c (i : var_i) xs :
  disj_fvars (Sv.add i xs)
  -> disj_fvars (vars_lval (Lvar i)) /\ disj_fvars xs.
Proof.
  move=> /disjoint_add [hi hxs].
  split; last exact hxs.
  apply: disjoint_equal_l _ hi.
  apply: SvP.MP.equal_sym.
  exact: vars_lval_Lvar.
Qed.

Lemma disj_fvars_vars_l_read_es xs :
  disj_fvars (vars_l xs)
  -> disj_fvars (read_es [seq Pvar (mk_lvar x) | x <- xs ]).
Proof.
  elim: xs => // x xs hind.
  rewrite /=.
  move=> /disjoint_add [hfvx hfvxs].
  apply: disjoint_equal_l.
  - apply/SvP.MP.equal_sym. exact: read_es_cons.

  apply: union_disjoint _ (hind hfvxs).
  apply: disjoint_equal_l _ hfvx.
  clear hind hfvxs.

  apply/SvP.MP.equal_sym.
  exact: read_e_var.
Qed.

End DISJ_FVARS.
