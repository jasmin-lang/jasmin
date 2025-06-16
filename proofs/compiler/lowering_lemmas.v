From mathcomp Require Import ssreflect ssrfun ssrbool.

From lang Require Import
  expr
  low_memory
  psem.
Require Import
  lowering.

Section ESTATE_EQ_EXCEPT.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

(* State equality up to a set of variables. *)
Definition st_eq_ex ys s1 s2 := (st_rel eq_ex ys s1 s2).

(* FIXME syscall : why it is needed to redeclare it here *)
(* note that in utils, it is CMorphisms.Proper, here it is Morpisms.Proper *)
#[global]
Instance and3_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. apply and3_iff_morphism. Qed.
(* END FIXME syscall *)

Lemma eeq_excR xs s :
  st_eq_ex xs s s.
Proof. done. Qed.

Lemma eeq_excS xs s0 s1 :
  st_eq_ex xs s0 s1
  -> st_eq_ex xs s1 s0.
Proof. by rewrite /st_eq_ex /st_rel => -[-> -> ->]. Qed.

Lemma eeq_excT xs s0 s1 s2 :
  st_eq_ex xs s0 s1
  -> st_eq_ex xs s1 s2
  -> st_eq_ex xs s0 s2.
Proof. by rewrite /st_eq_ex /st_rel => -[-> -> ->]. Qed.

Lemma eeq_exc_disjoint xs ys s0 s1 :
  disjoint xs ys
  -> st_eq_ex ys s0 s1
  -> st_eq_on xs s0 s1.
Proof.
  rewrite /st_eq_ex /st_eq_on /st_rel.
  move=> /Sv.is_empty_spec hdisj [-> -> hvm].
  split=> // x hxxs.
  apply: hvm.
  SvD.fsetdec.
Qed.

Lemma eeq_exc_sem_pexprs wdb gd xs es v s0 s1 :
  disjoint (read_es es) xs
  -> st_eq_ex xs s0 s1
  -> sem_pexprs wdb gd s0 es = ok v
  -> sem_pexprs wdb gd s1 es = ok v.
Proof.
  move=> hdisj heq.
  have [hscs hmem hvm] := eeq_exc_disjoint hdisj heq.
  rewrite (read_es_eq_on wdb gd hvm).
  rewrite /with_vm.
  rewrite hscs hmem.
  by rewrite -(surj_estate s1).
Qed.

Lemma eeq_exc_sem_pexpr wdb gd xs e v s0 s1 :
  disjoint (read_e e) xs
  -> st_eq_ex xs s0 s1
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
  -> st_eq_ex xs s0 s0'
  -> write_lvals wdb gd s0 ls vs = ok s1
  -> exists2 s1',
       write_lvals wdb gd s0' ls vs = ok s1' & st_eq_ex xs s1 s1'.
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
  - move=> x hx. apply: hvm. SvD.fsetdec.

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
  -> st_eq_ex xs s0 s0'
  -> write_lval wdb gd l v s0 = ok s1
  -> exists2 s1',
       write_lval wdb gd l v s0' = ok s1' & st_eq_ex xs s1 s1'.
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
  -> st_eq_ex vs s0 s1
  -> get_gvar wdb gd (evm s0) x = get_gvar wdb gd (evm s1) x.
Proof.
  move=> /Sv_memP hx [hscs hmem hvm].
  rewrite /get_gvar /=.
  case: is_lvar; last done.
  rewrite /get_var /=.
  by rewrite (hvm _ hx).
Qed.

Lemma read_es_st_eq_ex gd wdb es X :
  disjoint (read_es es) X ->
  wrequiv (st_rel eq_ex X) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) eq.
Proof.
  move=> hdisj s t v hst he; exists v => //.
  by apply (eeq_exc_sem_pexprs hdisj hst he).
Qed.

Lemma write_lvals_st_eq_ex gd wdb xs vs X :
  disjoint (vars_lvals xs) X ->
  wrequiv
    (st_eq_ex X)
    (fun s1 => write_lvals wdb gd s1 xs vs) (fun s2 => write_lvals wdb gd s2 xs vs)
    (st_eq_ex X).
Proof. by move=> hdisj s t s'; apply eeq_exc_write_lvals. Qed.

Definition check_es_st_eq_ex (X:Sv.t) (es1 es2 : pexprs) (X':Sv.t) :=
  [/\ X' = X, es1 = es2 & disjoint (read_es es1) X].

(* Remark this is stronger than needed (read_rvs xs1 is sufficiant) but previous lemmas are done like that ... *)
Definition check_lvals_st_eq_ex (X:Sv.t) (xs1 xs2 : lvals) (X':Sv.t) :=
  [/\ X' = X, xs1 = xs2 & disjoint (vars_lvals xs1) X].

Lemma check_esP_R_st_eq_ex X es1 es2 X':
  check_es_st_eq_ex X es1 es2 X' -> forall s1 s2, st_eq_ex X s1 s2 -> st_eq_ex X' s1 s2.
Proof. by move=> [-> _ _]. Qed.

Definition checker_st_eq_ex : Checker_e st_eq_ex :=
  {| check_es := check_es_st_eq_ex;
     check_lvals := check_lvals_st_eq_ex;
     check_esP_rel := check_esP_R_st_eq_ex |}.

Section CALL.
Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

Lemma st_eq_ex_finalize fd fd' X:
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  disjoint (vars_l (f_res fd)) X ->
  wrequiv (st_eq_ex X) (finalize_funcall fd) (finalize_funcall fd') eq.
Proof.
  move=> ??? hdisj.
  apply wrequiv_weaken with (st_eq_on (vars_l (f_res fd))) eq => //.
  + move=> s t [h1 h2 h3]; split => //.
    by apply: (eq_ex_disjoint_eq_on h3); apply disjoint_sym.
  by apply st_eq_on_finalize.
Qed.

Context (p p':prog).

Local Notation gd := (p_globs p).
Local Notation gd' := (p_globs p').

Context (eq_globs : gd = gd').

Lemma checker_st_eq_exP : Checker_eq p p' checker_st_eq_ex.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [? -> ?]; apply read_es_st_eq_ex.
  move=> wdb ? d xs1 xs2 d' /wdb_ok_eq <- [-> <- hdisj] vs.
  by apply write_lvals_st_eq_ex.
Qed.

End CALL.

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

Lemma disj_fvars_vars_I_Cwhile ii al c0 e ei c1 :
  disj_fvars (vars_I (MkI ii (Cwhile al c0 e ei c1)))
  -> [/\ disj_fvars (vars_c c0)
       , disj_fvars (read_e e)
       & disj_fvars (vars_c c1)
     ].
Proof.
  move=> /(disjoint_equal_l (vars_I_while ii al c0 e ei c1)).
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
