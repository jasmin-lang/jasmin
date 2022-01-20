From mathcomp Require Import all_ssreflect all_algebra.
Require Import Utf8.
Require Export expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma is_lvar_is_glob x : is_lvar x = ~~is_glob x.
Proof. by case: x => ? []. Qed.

Section PEXPR_IND.
  Context
    (P: pexpr → Prop)
    (Hconst: ∀ z, P (Pconst z))
    (Hbool: ∀ b, P (Pbool b))
    (Harr_init: ∀ n, P (Parr_init n))
    (Hvar: ∀ x, P (Pvar x))
    (Hget: ∀ aa sz x e, P e → P (Pget aa sz x e))
    (Hsub:  ∀ aa sz len x e, P e  → P (Psub aa sz len x e))
    (Hload: ∀ sz x e, P e → P (Pload sz x e))
    (Happ1: ∀ op e, P e → P (Papp1 op e))
    (Happ2: ∀ op e1, P e1 → ∀ e2, P e2 → P (Papp2 op e1 e2))
    (HappN: ∀ op es, (∀ e, e \in es → P e) → P (PappN op es))
    (Hif: ∀ t e, P e → ∀ e1, P e1 → ∀ e2, P e2 → P (Pif t e e1 e2))
  .

  Definition pexpr_ind_rec (f: ∀ e, P e) : ∀ es : pexprs, ∀ e, e \in es → P e.
  refine
    (fix loop es :=
       if es is e :: es'
       then λ (e: pexpr), _
       else λ e (k: e \in [::]), False_ind _ (Bool.diff_false_true k)
    ).
  rewrite in_cons; case/orP.
  + move => /eqP -> ; exact: f.
  apply: loop.
  Defined.

  Fixpoint pexpr_ind (e: pexpr) : P e :=
    match e with
    | Pconst z => Hconst z
    | Pbool b => Hbool b
    | Parr_init n => Harr_init n
    | Pvar x => Hvar x
    | Pget aa sz x e => Hget aa sz x (pexpr_ind e)
    | Psub aa sz len x e => Hsub aa sz len x (pexpr_ind e)
    | Pload sz x e => Hload sz x (pexpr_ind e)
    | Papp1 op e => Happ1 op (pexpr_ind e)
    | Papp2 op e1 e2 => Happ2 op (pexpr_ind e1) (pexpr_ind e2)
    | PappN op es => HappN op (@pexpr_ind_rec pexpr_ind es)
    | Pif t e e1 e2 => Hif t (pexpr_ind e) (pexpr_ind e1) (pexpr_ind e2)
    end.

End PEXPR_IND.

(* Mutual induction scheme for pexpr and pexprs *)
Section PEXPRS_IND.
  Context
    (P: pexpr → Prop)
    (Q: pexprs → Prop)
  .

  Record pexpr_ind_hypotheses : Prop := {
    pexprs_nil: Q [::];
    pexprs_cons: ∀ pe, P pe → ∀ pes, Q pes → Q (pe :: pes);
    pexprs_const: ∀ z, P (Pconst z);
    pexprs_bool: ∀ b, P (Pbool b);
    pexprs_arr_init: ∀ n, P (Parr_init n);
    pexprs_var: ∀ x, P (Pvar x);
    pexprs_get: ∀ aa sz x e, P e → P (Pget aa sz x e);
    pexprs_sub: ∀ aa sz len x e, P e → P (Psub aa sz len x e);
    pexprs_load: ∀ sz x e, P e → P (Pload sz x e);
    pexprs_app1: ∀ op e, P e → P (Papp1 op e);
    pexprs_app2: ∀ op e1, P e1 → ∀ e2, P e2 → P (Papp2 op e1 e2);
    pexprs_appN: ∀ op es, Q es → P (PappN op es);
    pexprs_if: ∀ t e, P e → ∀ e1, P e1 → ∀ e2, P e2 → P (Pif t e e1 e2);
  }.

  Context (h: pexpr_ind_hypotheses).

  Definition pexprs_ind pexpr_mut_ind : ∀ pes, Q pes :=
    fix pexprs_ind pes :=
      if pes is pe :: pes'
      then pexprs_cons h (pexpr_mut_ind pe) (pexprs_ind pes')
      else pexprs_nil h.

  Fixpoint pexpr_mut_ind pe : P pe :=
    match pe with
    | Pconst z => pexprs_const h z
    | Pbool b => pexprs_bool h b
    | Parr_init n => pexprs_arr_init h n
    | Pvar x => pexprs_var h x
    | Pget aa sz x e => pexprs_get h aa sz x (pexpr_mut_ind e)
    | Psub aa sz len x e => pexprs_sub h aa sz len x (pexpr_mut_ind e)
    | Pload sz x e => pexprs_load h sz x (pexpr_mut_ind e)
    | Papp1 op e => pexprs_app1 h op (pexpr_mut_ind e)
    | Papp2 op e1 e2 => pexprs_app2 h op (pexpr_mut_ind e1) (pexpr_mut_ind e2)
    | PappN op es => pexprs_appN h op (pexprs_ind pexpr_mut_ind es)
    | Pif t e e1 e2 => pexprs_if h t (pexpr_mut_ind e) (pexpr_mut_ind e1) (pexpr_mut_ind e2)
    end.

  Definition pexprs_ind_pair :=
    conj pexpr_mut_ind (pexprs_ind pexpr_mut_ind).

End PEXPRS_IND.

Section ASM_OP.

Context `{asmop:asmOp}.
Context {eft} {pT : progT eft}.

Section CMD_RECT.
  Variables (Pr:instr_r -> Type) (Pi:instr -> Type) (Pc : cmd -> Type).
  Hypothesis Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Hypothesis Hnil : Pc [::].
  Hypothesis Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Hypothesis Hopn : forall xs t o es, Pr (Copn xs t o es).
  Hypothesis Hsyscall : forall xs o es, Pr (Csyscall xs o es).
  Hypothesis Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Hypothesis Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Hypothesis Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Hypothesis Hcall: forall i xs f es, Pr (Ccall i xs f es).

  Section C.
  Variable instr_rect : forall i, Pi i.

  Fixpoint cmd_rect_aux (c:cmd) : Pc c :=
    match c return Pc c with
    | [::] => Hnil
    | i::c => @Hcons i c (instr_rect i) (cmd_rect_aux c)
    end.
  End C.

  Fixpoint instr_Rect (i:instr) : Pi i :=
    match i return Pi i with
    | MkI ii i => @Hmk i ii (instr_r_Rect i)
    end
  with instr_r_Rect (i:instr_r) : Pr i :=
    match i return Pr i with
    | Cassgn x tg ty e => Hasgn x tg ty e
    | Copn xs t o es => Hopn xs t o es
    | Csyscall xs o es => Hsyscall xs o es
    | Cif e c1 c2  => @Hif e c1 c2 (cmd_rect_aux instr_Rect c1) (cmd_rect_aux instr_Rect c2)
    | Cfor i (dir,lo,hi) c => @Hfor i dir lo hi c (cmd_rect_aux instr_Rect c)
    | Cwhile a c e c'   => @Hwhile a c e c' (cmd_rect_aux instr_Rect c) (cmd_rect_aux instr_Rect c')
    | Ccall ii xs f es => @Hcall ii xs f es
    end.

  Definition cmd_rect := cmd_rect_aux instr_Rect.

End CMD_RECT.

Lemma surj_prog (p:prog) : 
  {| p_globs := p_globs p; p_funcs := p_funcs p; p_extra := p_extra p |} = p.
Proof. by case: p. Qed.

(* ----------------------------------------------------------------------------- *)
Lemma get_fundef_cons {T} (fnd: funname * T) p fn:
  get_fundef (fnd :: p) fn = if fn == fnd.1 then Some fnd.2 else get_fundef p fn.
Proof. by case: fnd. Qed.

Lemma get_fundef_in {T} {p f} {fd: T} : get_fundef p f = Some fd -> f \in [seq x.1 | x <- p].
Proof. by rewrite/get_fundef; apply: assoc_mem_dom'. Qed.

Lemma get_fundef_in' {T} {p fn} {fd: T}:
  get_fundef p fn = Some fd -> List.In (fn, fd) p.
Proof. exact: assoc_mem'. Qed.

Definition all_prog {aT bT cT} (s1: seq (funname * aT)) (s2: seq (funname * bT)) (ll: seq cT) f :=
  (size s1 == size s2) && all2 (fun fs a => let '(fd1, fd2) := fs in (fd1.1 == fd2.1) && f a fd1.2 fd2.2) (zip s1 s2) ll.

Lemma all_progP {aT bT cT} (s1: seq (funname * aT)) (s2: seq (funname * bT)) (l: seq cT) f:
  all_prog s1 s2 l f ->
  forall fn fd, get_fundef s1 fn = Some fd ->
  exists fd' l', get_fundef s2 fn = Some fd' /\ f l' fd fd'.
Proof.
elim: s1 s2 l=> // [[fn fd] p IH] [|[fn' fd'] p'] // [|lh la] //.
+ by rewrite /all_prog /= andbF.
+ move=> /andP [/= Hs /andP [/andP [/eqP Hfn Hfd] Hall]].
  move=> fn0 fd0.
  case: ifP=> /eqP Hfn0.
  + move=> [] <-.
    exists fd', lh.
    rewrite -Hfn Hfn0 /= eq_refl; split=> //.
  + move=> H.
    have [|fd'' [l' [IH1 IH2]]] := (IH p' la _ _ _ H).
    apply/andP; split.
    by rewrite -eqSS.
    exact: Hall.
    exists fd'', l'; split=> //.
    rewrite /= -Hfn.
    by case: ifP=> // /eqP.
Qed.

(* ** Some smart constructors
 * -------------------------------------------------------------------------- *)

Variant is_reflect (A:Type) (P:A -> pexpr) : pexpr -> option A -> Prop :=
 | Is_reflect_some : forall a, is_reflect P (P a) (Some a)
 | Is_reflect_none : forall e, is_reflect P e None.

Lemma is_boolP e : is_reflect Pbool e (is_bool e).
Proof. by case e=> *;constructor. Qed.

Lemma is_constP e : is_reflect Pconst e (is_const e).
Proof. by case: e=>*;constructor. Qed.

Lemma is_reflect_some_inv {A P e a} (H: @is_reflect A P e (Some a)) : e = P a.
Proof.
  set (d e m := match m with None => True | Some a => e = P a end).
  change (d e (Some a)).
  case H; simpl; auto.
Qed.

Lemma is_wconst_of_sizeP sz e :
  is_reflect (fun z => Papp1 (Oword_of_int sz) (Pconst z)) e (is_wconst_of_size sz e).
Proof.
case: e; try constructor.
case; try constructor.
move => sz' []; try constructor.
move => z /=; case: eqP; try constructor.
move => ->; exact: Is_reflect_some.
Qed.

(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Instance vrv_rec_m : Proper (Sv.Equal ==> eq ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs x r ->;case:r => //= [v | _ _ v _ | _ _ _ v _]; SvD.fsetdec.
Qed.

Lemma vrv_none i t: vrv (Lnone i t) = Sv.empty.
Proof. by []. Qed.

Lemma vrv_var x: Sv.Equal (vrv (Lvar x)) (Sv.singleton x).
Proof. rewrite /=; clear; SvD.fsetdec. Qed.

Lemma vrv_mem w x e : vrv (Lmem w x e) = Sv.empty.
Proof. by []. Qed.

Lemma vrv_aset aa w x e : Sv.Equal (vrv (Laset aa w x e)) (Sv.singleton x).
Proof. rewrite /=; clear; SvD.fsetdec. Qed.

Lemma vrv_recE s (r:lval) : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
  case: r => *; rewrite ?vrv_none ?vrv_var ?vrv_mem ?vrv_aset /=; clear; SvD.fsetdec.
Qed.

Lemma vrvs_recE s rs : Sv.Equal (vrvs_rec s rs) (Sv.union s (vrvs rs)).
Proof.
  rewrite /vrvs;elim: rs s => [|r rs Hrec] s /=;first by clear; SvD.fsetdec.
  rewrite !(Hrec (vrv_rec _ _)) (vrv_recE s); clear; SvD.fsetdec.
Qed.

Lemma vrvs_cons r rs : Sv.Equal (vrvs (r::rs)) (Sv.union (vrv r) (vrvs rs)).
Proof. by rewrite /vrvs /= vrvs_recE. Qed.

Lemma write_c_recE s c : Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
           (fun i => forall s, Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)))
           (fun c => forall s, Sv.Equal (foldl write_I_rec s c) (Sv.union s (write_c c)))) =>
     /= {c s}
    [ i ii Hi | | i c Hi Hc | x tg ty e | xs t o es | p x e | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | a c e c' Hc Hc' | ii xs f es ] s;
    rewrite /write_I /write_I_rec /write_i /write_i_rec -/write_i_rec -/write_I_rec /write_c /=
    ?Hc1 ?Hc2 /write_c_rec ?Hc ?Hc' ?Hi -?vrv_recE -?vrvs_recE //;
    by clear; SvD.fsetdec.
Qed.

Lemma write_I_recE s i : Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)).
Proof. by apply (write_c_recE s [:: i]). Qed.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. by apply (write_I_recE s (MkI 1%positive i)). Qed.

Lemma write_c_nil : write_c [::] = Sv.empty.
Proof. done. Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_I i) (write_c c)).
Proof. rewrite {1}/write_c /= write_c_recE write_I_recE; clear; SvD.fsetdec. Qed.

Lemma write_c_app c1 c2 :
  Sv.Equal (write_c (c1 ++ c2)) (Sv.union (write_c c1) (write_c c2)).
Proof. by elim: c1 => //= i c1 Hrec;rewrite !write_c_cons; clear -Hrec; SvD.fsetdec. Qed.

Lemma write_i_assgn x tag ty e : write_i (Cassgn x tag ty e) = vrv x.
Proof. done. Qed.

Lemma write_i_opn xs t o es : write_i (Copn xs t o es) = vrvs xs.
Proof. done. Qed.

Lemma write_i_syscall xs o es : write_i (Csyscall xs o es) = vrvs xs.
Proof. done. Qed.

Lemma write_i_if e c1 c2 :
  Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /write_i_rec -/write_I_rec -/(write_c_rec _ c1) -/(write_c_rec _ c2) !write_c_recE;
    clear; SvD.fsetdec.
Qed.

Lemma write_i_for x rn c :
  Sv.Equal (write_i (Cfor x rn c)) (Sv.union (Sv.singleton x) (write_c c)).
Proof.
  rewrite /write_i /write_i_rec -/write_I_rec -/(write_c_rec _ c) write_c_recE;
    clear; SvD.fsetdec.
Qed.

Lemma write_i_while a c e c' :
  Sv.Equal (write_i (Cwhile a c e c')) (Sv.union (write_c c) (write_c c')).
Proof.
  rewrite /write_i /write_i_rec -/write_I_rec -/(write_c_rec _ c) write_c_recE;
    clear; SvD.fsetdec.
Qed.

Lemma write_i_call ii xs f es :
  write_i (Ccall ii xs f es) = vrvs xs.
Proof. done. Qed.

Lemma write_Ii ii i: write_I (MkI ii i) = write_i i.
Proof. by done. Qed.

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Lemma read_eE e s : Sv.Equal (read_e_rec s e) (Sv.union (read_e e) s).
Proof.
  elim: e s => //= [v | aa w v e He | aa w len v e He | w v e He | o e1 He1 e2 He2 | o es Hes | t e He e1 He1 e2 He2] s;
   rewrite /read_e /= ?He ?He1 ?He2; try (clear; SvD.fsetdec).
  rewrite -/read_es_rec -/read_es.
  elim: es Hes s.
  + by move => _ /= s; clear; SvD.fsetdec.
  move => e es ih Hes s /=.
  rewrite /read_es /= -/read_e ih.
  + rewrite Hes.
    + rewrite ih.
      + by clear; SvD.fsetdec.
      move => e' he' s'; apply: Hes.
      by rewrite in_cons he' orbT.
    by rewrite in_cons eqxx.
  move => e' he' s'; apply: Hes.
  by rewrite in_cons he' orbT.
Qed.

Lemma read_e_var (x:gvar) : Sv.Equal (read_e (Pvar x))(read_gvar x).
Proof. rewrite /read_e /= /read_gvar;case:ifP => _; clear; SvD.fsetdec. Qed.

Lemma read_esE es s : Sv.Equal (read_es_rec s es) (Sv.union (read_es es) s).
Proof.
  elim: es s => [ | e es Hes] s;rewrite /read_es /= ?Hes ?read_eE; clear; SvD.fsetdec.
Qed.

Lemma read_es_cons e es :
  Sv.Equal (read_es (e :: es)) (Sv.union (read_e e) (read_es es)).
Proof. by rewrite /read_es /= !read_esE read_eE; clear; SvD.fsetdec. Qed.

Lemma read_rvE s x: Sv.Equal (read_rv_rec s x) (Sv.union s (read_rv x)).
Proof.
  case: x => //= *; rewrite /read_rv /= ?read_eE; clear; SvD.fsetdec.
Qed.

Lemma read_rvsE s xs:  Sv.Equal (read_rvs_rec s xs) (Sv.union s (read_rvs xs)).
Proof.
  elim: xs s => [ |x xs Hxs] s;rewrite /read_rvs /= ?Hxs ?read_rvE; clear; SvD.fsetdec.
Qed.

Lemma read_rvs_nil : read_rvs [::] = Sv.empty.
Proof. done. Qed.

Lemma read_rvs_cons x xs : Sv.Equal (read_rvs (x::xs)) (Sv.union (read_rv x) (read_rvs xs)).
Proof.
  rewrite {1}/read_rvs /= read_rvsE read_rvE; clear; SvD.fsetdec.
Qed.

Lemma read_cE s c : Sv.Equal (read_c_rec s c) (Sv.union s (read_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)))
           (fun i => forall s, Sv.Equal (read_I_rec s i) (Sv.union s (read_I i)))
           (fun c => forall s, Sv.Equal (foldl read_I_rec s c) (Sv.union s (read_c c))))
           => /= {c s}
   [ i ii Hi | | i c Hi Hc | x tg ty e | xs t o es | p x e | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | a c e c' Hc Hc' | ii xs f es ] s;
    rewrite /read_I /read_I_rec /read_i /read_i_rec -/read_i_rec -/read_I_rec /read_c /=
     ?read_rvE ?read_eE ?read_esE ?read_rvE ?read_rvsE ?Hc2 ?Hc1 /read_c_rec ?Hc' ?Hc ?Hi //;
    by clear; SvD.fsetdec.
Qed.

Lemma read_IE s i : Sv.Equal (read_I_rec s i) (Sv.union s (read_I i)).
Proof. by apply (read_cE s [:: i]). Qed.

Lemma read_iE s i : Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)).
Proof. by apply (read_IE s (MkI 1%positive i)). Qed.

Lemma read_c_nil : read_c [::] = Sv.empty.
Proof. done. Qed.

Lemma read_c_cons i c: Sv.Equal (read_c (i::c)) (Sv.union (read_I i) (read_c c)).
Proof. by rewrite {1}/read_c /= read_cE //. Qed.

Lemma read_i_assgn x tag ty e :
  Sv.Equal (read_i (Cassgn x tag ty e)) (Sv.union (read_rv x) (read_e e)).
Proof. rewrite /read_i /read_i_rec read_rvE read_eE; clear; SvD.fsetdec. Qed.

Lemma read_i_opn xs t o es:
  Sv.Equal (read_i (Copn xs t o es)) (Sv.union (read_rvs xs) (read_es es)).
Proof. by rewrite /read_i /read_i_rec read_esE read_rvsE; clear; SvD.fsetdec. Qed.

Lemma read_i_syscall xs o es :
  Sv.Equal (read_i (Csyscall xs o es)) (Sv.union (read_rvs xs) (read_es es)).
Proof. rewrite /read_i /read_i_rec read_esE read_rvsE; clear; SvD.fsetdec. Qed.

Lemma read_i_if e c1 c2 :
   Sv.Equal (read_i (Cif e c1 c2)) (Sv.union (read_e e) (Sv.union (read_c c1) (read_c c2))).
Proof.
  rewrite /read_i /read_i_rec -/read_c_rec read_eE !read_cE; clear; SvD.fsetdec.
Qed.

Lemma read_i_for x dir lo hi c :
   Sv.Equal (read_i (Cfor x (dir, lo, hi) c))
            (Sv.union (read_e lo) (Sv.union (read_e hi) (read_c c))).
Proof.
  rewrite /read_i /read_i_rec -/read_c_rec !read_eE read_cE; clear; SvD.fsetdec.
Qed.

Lemma read_i_while a c e c' :
   Sv.Equal (read_i (Cwhile a c e c'))
            (Sv.union (read_c c) (Sv.union (read_e e) (read_c c'))).
Proof.
  rewrite /read_i /read_i_rec -/read_c_rec !read_eE read_cE; clear; SvD.fsetdec.
Qed.

Lemma read_i_call ii xs f es :
  Sv.Equal (read_i (Ccall ii xs f es)) (Sv.union (read_rvs xs) (read_es es)).
Proof. rewrite /read_i /read_i_rec read_esE read_rvsE; clear; SvD.fsetdec. Qed.

Lemma read_Ii ii i: read_I (MkI ii i) = read_i i.
Proof. by done. Qed.

(* ** Compute occurring variables (= read + write)
 * -------------------------------------------------------------------------- *)

Lemma vars_l_read_es (l:seq var_i) : Sv.Equal (read_es [seq (Pvar (mk_lvar i)) | i <- l]) (vars_l l).
Proof.
  elim: l => //= x xs hrec; rewrite read_es_cons /= read_e_var /read_gvar /= hrec;
    clear; SvD.fsetdec.
Qed.

Lemma vars_c_cons i c:
  Sv.Equal (vars_c (i :: c)) (Sv.union (vars_I i) (vars_c c)).
Proof.
  rewrite /vars_c read_c_cons write_c_cons /vars_I.
  move: (read_I i) (read_c c) (write_I i) (write_c c). (* SvD.fsetdec faster *)
  clear; SvD.fsetdec.
Qed.

Lemma vars_I_assgn ii l tag ty e:
  Sv.Equal (vars_I (MkI ii (Cassgn l tag ty e))) (Sv.union (vars_lval l) (read_e e)).
Proof. by rewrite /vars_I read_Ii write_Ii read_i_assgn write_i_assgn /vars_lval; clear; SvD.fsetdec. Qed.

Lemma vars_I_opn ii xs t o es:
  Sv.Equal (vars_I (MkI ii (Copn xs t o es))) (Sv.union (vars_lvals xs) (read_es es)).
Proof. by rewrite /vars_I read_Ii write_Ii read_i_opn write_i_opn /vars_lvals; clear; SvD.fsetdec. Qed.

Lemma vars_I_if ii e c1 c2:
  Sv.Equal (vars_I (MkI ii (Cif e c1 c2))) (Sv.union (read_e e) (Sv.union (vars_c c1) (vars_c c2))).
Proof.
  rewrite /vars_I read_Ii write_Ii read_i_if write_i_if /vars_c.
  move: (read_e e) (read_c c1) (read_c c2) (write_c c1) (write_c c2). (* SvD.fsetdec faster *)
  clear; SvD.fsetdec.
Qed.

Lemma vars_I_while ii a c e c':
  Sv.Equal (vars_I (MkI ii (Cwhile a c e c'))) (Sv.union (read_e e) (Sv.union (vars_c c) (vars_c c'))).
Proof.
  rewrite /vars_I read_Ii write_Ii read_i_while write_i_while /vars_c.
  move: (read_c c) (read_e e) (read_c c') (write_c c) (write_c c'). (* SvD.fsetdec faster *)
  clear; SvD.fsetdec.
Qed.

Lemma vars_I_for ii i d lo hi c:
  Sv.Equal (vars_I (MkI ii (Cfor i (d, lo, hi) c)))
           (Sv.union (Sv.union (vars_c c) (Sv.singleton i)) (Sv.union (read_e lo) (read_e hi))).
Proof. rewrite /vars_I read_Ii write_Ii read_i_for write_i_for /vars_c; clear; SvD.fsetdec. Qed.

Lemma vars_I_call ii ii' xs fn args:
  Sv.Equal (vars_I (MkI ii (Ccall ii' xs fn args))) (Sv.union (vars_lvals xs) (read_es args)).
Proof. rewrite /vars_I read_Ii write_Ii read_i_call write_i_call /vars_lvals; clear; SvD.fsetdec. Qed.

Lemma vars_pP p fn fd : get_fundef p fn = Some fd -> Sv.Subset (vars_fd fd) (vars_p p).
Proof.
  elim: p => //= -[fn' fd'] p hrec; case: eqP => [ _ [<-] | ]; first by clear; SvD.fsetdec.
  move=> _ /hrec; clear; SvD.fsetdec.
Qed.

End ASM_OP.

(* --------------------------------------------------------------------- *)
(* Test the equality of two expressions modulo variable info             *)

Lemma eq_gvar_refl x : eq_gvar x x.
Proof. by rewrite /eq_gvar ?eqxx. Qed.

Lemma eq_expr_refl e : eq_expr e e.
Proof.
elim: e => //= [ ? | ???? -> | ????? -> |??? -> | ?? -> | ?? -> ? -> | ? es ih | ??-> ? -> ? -> ] //=;
  rewrite ?eqxx ?eq_gvar_refl //=.
elim: es ih => // e es ih h /=; rewrite h.
+ by apply: ih => e' he'; apply: h; rewrite in_cons he' orbT.
by rewrite in_cons eqxx.
Qed.

Lemma eq_gvar_trans x2 x1 x3 : eq_gvar x1 x2 → eq_gvar x2 x3 → eq_gvar x1 x3.
Proof. by rewrite /eq_gvar => /andP[] /eqP -> /eqP -> /andP[] /eqP -> /eqP ->; rewrite !eqxx. Qed.

Lemma eq_expr_trans e2 e1 e3 : 
  eq_expr e1 e2 -> eq_expr e2 e3 -> eq_expr e1 e3.
Proof.
  elim: e1 e2 e3.
  1-3: by move=> ? [] // ? [] //= ? /eqP -> /eqP ->.
  + by move=> x1 [] // x2 [] //= x3; apply eq_gvar_trans.
  + move=> ???? hrec [] //= ???? [] //= ????.
    move=> /andP[]/andP[]/andP[]/eqP -> /eqP -> hx1 /hrec h1.
    move=> /andP[]/andP[]/andP[]/eqP -> /eqP -> hx2 /h1 ->.
    by rewrite !eqxx (eq_gvar_trans hx1 hx2).
  + move=> ????? hrec [] //= ????? [] //= ?????.
    move=> /andP[]/andP[]/andP[]/andP[]/eqP -> /eqP -> /eqP -> hx1 /hrec h1.
    move=> /andP[]/andP[]/andP[]/andP[]/eqP -> /eqP -> /eqP -> hx2 /h1 ->.
    by rewrite !eqxx (eq_gvar_trans hx1 hx2).
  + move=> ??? hrec [] //= ??? [] //= ???.
    move=> /andP[]/andP[]/eqP-> /eqP-> /hrec h1.
    by move=> /andP[]/andP[]/eqP-> /eqP-> /h1 ->; rewrite !eqxx.
  + move=> ?? hrec [] //= ?? [] //= ??.
    move=> /andP[] /eqP-> /hrec h1.
    by move=> /andP[] /eqP-> /h1 ->; rewrite eqxx.
  + move=> ?? hrec1 ? hrec2 [] //= ??? [] //= ???.
    move=> /andP[]/andP[]/eqP-> /hrec1 h1 /hrec2 h2.
    by move=> /andP[]/andP[]/eqP-> /h1 -> /h2 ->; rewrite !eqxx.
  + move=> o es1 hrec [] //= ? es2 [] ? es3 //=.
    move=> /andP[]/eqP-> h1 /andP[]/eqP-> h2;rewrite eqxx /=.
    elim: es1 hrec es2 es3 h1 h2 => [ | e1 es1 hrecs] hrec [] // e2 es2 [] //= e3 es3.
    move=> /andP[]/hrec h1 /hrecs hs /andP[] /h1 ->; last by rewrite inE eqxx.
    by move=> /hs -> // e hin; apply hrec; rewrite inE hin orbT.
  move=> ?? hrec ? hrec1 ? hrec2 []//= ???? []//= ????.
  move=> /andP[]/andP[]/andP[] /eqP-> /hrec h /hrec1 h1 /hrec2 h2.
  by move=> /andP[]/andP[]/andP[] /eqP-> /h -> /h1 -> /h2 ->; rewrite eqxx.
Qed.

Lemma eq_lval_refl x : eq_lval x x.
Proof.
  by case: x => // [ i ty | x | w x e | aa w x e | aa w len x e] /=; rewrite !eqxx // eq_expr_refl.
Qed.

Lemma eq_expr_constL z e :
  eq_expr (Pconst z) e -> e = z :> pexpr.
Proof. by case: e => // z' /eqP ->. Qed.

Lemma eq_expr_const z1 z2 :
  eq_expr (Pconst z1) (Pconst z2) -> z1 = z2.
Proof. by move/eqP. Qed.

Lemma eq_expr_var x1 x2 :
  eq_expr (Pvar x1) (Pvar x2) -> x1.(gs) = x2.(gs) /\ x1.(gv) = x2.(gv) :> var.
Proof. by move => /andP[]/eqP -> /eqP ->. Qed.

Lemma eq_expr_load w1 w2 v1 v2 e1 e2 :
     eq_expr (Pload w1 v1 e1) (Pload w2 v2 e2)
  -> [/\ w1 = w2, v1 = v2 :> var & eq_expr e1 e2].
Proof. by move=> /= /andP [/andP[]] /eqP-> /eqP-> ->. Qed.

Lemma eq_expr_app1 o1 o2 e1 e2 :
     eq_expr (Papp1 o1 e1) (Papp1 o2 e2)
  -> [/\ o1 = o2 & eq_expr e1 e2].
Proof. by move=> /= /andP[/eqP-> ->]. Qed.
