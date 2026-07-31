From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import psem.
Require Export normalize_cond.

Section NORMALIZE_COND_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (normalize_cond_ok : normalize_cond_prog p = p')
.

Lemma sem_sop2_gt_ltP k v1 v2 v :
  sem_sop2 (Ogt k) v1 v2 = ok v ->
  sem_sop2 (Olt k) v2 v1 = ok v.
Proof.
rewrite /sem_sop2 /=.
case: k => [|u sz] /=; last by t_xrbindP=> x1 -> x2 -> <-.
by t_xrbindP=> x1 -> x2 -> <-; rewrite Z.gtb_ltb.
Qed.

Lemma sem_sop2_ge_leP k v1 v2 v :
  sem_sop2 (Oge k) v1 v2 = ok v ->
  sem_sop2 (Ole k) v2 v1 = ok v.
Proof.
rewrite /sem_sop2 /=.
case: k => [|u sz] /=; last by t_xrbindP=> x1 -> x2 -> <-.
by t_xrbindP=> x1 -> x2 -> <-; rewrite Z.geb_leb.
Qed.

Lemma sem_sop2_normalizeP o v1 v2 v :
  sem_sop2 o v1 v2 = ok v ->
  match o with
  | Ogt k => sem_sop2 (Olt k) v2 v1
  | Oge k => sem_sop2 (Ole k) v2 v1
  | _ => sem_sop2 o v1 v2
  end = ok v.
Proof.
case: o => //= c; first exact: sem_sop2_gt_ltP.
exact: sem_sop2_ge_leP.
Qed.

Lemma normalize_cond_eP wdb gd s :
  (forall e v,
      sem_pexpr wdb gd s e = ok v ->
      sem_pexpr wdb gd s (normalize_cond_e e) = ok v)
  /\
  (forall es vs,
      sem_pexprs wdb gd s es = ok vs ->
      sem_pexprs wdb gd s (normalize_cond_es es) = ok vs).
Proof.
apply: pexprs_ind_pair; constructor.
- by [].
- move=> pe ih1 pes ih2 vs /=; rewrite /sem_pexprs /=.
  t_xrbindP=> v hv vs' hvs' <-.
  rewrite (ih1 _ hv) /=.
  by have := ih2 vs'; rewrite /sem_pexprs => -> //.
- by [].
- by [].
- by [].
- by [].
- move=> al aa sz x e ih v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; rewrite hz /=; t_xrbindP=> i x0 hx0 hi w hw <-.
  by rewrite (ih _ hx0) /= hi /= hw.
- move=> aa sz len x e ih v /=; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; rewrite hz /=; t_xrbindP=> i x0 hx0 hi t' ht' <-.
  by rewrite (ih _ hx0) /= hi /= ht'.
- move=> al sz e ih v /=; t_xrbindP=> wp x0 hx0 hwp w hw <-.
  by rewrite (ih _ hx0) /= hwp /= hw.
- move=> op e ih v /=; t_xrbindP=> x0 hx0 hop.
  by rewrite (ih _ hx0) /= hop.
- move=> op e1 ih1 e2 ih2 v /=; t_xrbindP=> v1 hv1 v2 hv2 hop.
  have hv1' := ih1 _ hv1.
  have hv2' := ih2 _ hv2.
  have hs := sem_sop2_normalizeP hop.
  by case: op hop hs => //=; move=> *; rewrite hv1' /= hv2'.
- move=> op es ihs v /=; t_xrbindP=> vs hvs hop.
  have -> :
    mapM (sem_pexpr wdb gd s) [seq normalize_cond_e i | i <- es] = ok vs.
  + exact: ihs _ hvs.
  by rewrite /= hop.
move=> t e0 ih0 e1 ih1 e2 ih2 v /=.
t_xrbindP=> b0 x0 hx0 hb0 t1 x1 hx1 ht1 t2 x2 hx2 ht2 <-.
by rewrite (ih0 _ hx0) /= hb0 /= (ih1 _ hx1) /= ht1 /= (ih2 _ hx2) /= ht2.
Qed.

Lemma normalize_cond_eP1 wdb gd s e v :
  sem_pexpr wdb gd s e = ok v ->
  sem_pexpr wdb gd s (normalize_cond_e e) = ok v.
Proof. exact: (normalize_cond_eP wdb gd s).1. Qed.

Lemma normalize_cond_eP2 wdb gd s es vs :
  sem_pexprs wdb gd s es = ok vs ->
  sem_pexprs wdb gd s (normalize_cond_es es) = ok vs.
Proof. exact: (normalize_cond_eP wdb gd s).2. Qed.

Lemma normalize_cond_lvalP wdb gd s x v s' :
  write_lval wdb gd x v s = ok s' ->
  write_lval wdb gd (normalize_cond_lval x) v s = ok s'.
Proof.
case: x => //=.
- move=> al sz vi e; t_xrbindP=> pt x0 hx0 hpt w hw m hm <-.
  by rewrite (normalize_cond_eP1 hx0) /= hpt /= hw /= hm.
- move=> al aa ws x0 e; rewrite /on_arr_var /=; t_xrbindP=> z hz.
  case: z hz => // n t hz; rewrite hz /=.
  t_xrbindP=> i x1 hx1 hi w hw t0 ht0 <-.
  by rewrite (normalize_cond_eP1 hx1) /= hi /= hw /= ht0.
move=> aa ws z x0 e; rewrite /on_arr_var /=; t_xrbindP=> z0 hz0.
case: z0 hz0 => // n t hz0; rewrite hz0 /=.
t_xrbindP=> i x1 hx1 hi t' ht' t0 ht0 <-.
by rewrite (normalize_cond_eP1 hx1) /= hi /= ht' /= ht0.
Qed.

Lemma normalize_cond_lvalsP wdb gd s xs vs s' :
  write_lvals wdb gd s xs vs = ok s' ->
  write_lvals wdb gd s (normalize_cond_lvals xs) vs = ok s'.
Proof.
rewrite /write_lvals /normalize_cond_lvals.
elim: xs vs s => [|x xs ih] [|v vs] //= s.
t_xrbindP=> s1 hx hxs.
by rewrite (normalize_cond_lvalP hx) /= (ih _ _ hxs).
Qed.

Lemma normalize_cond_eassertP gd s a b :
  sem_eassert gd s a = ok b ->
  sem_eassert gd s (normalize_cond_eassert a) = ok b.
Proof.
elim: a b => //=.
- move=> e b; t_xrbindP=> x0 hx0 hb.
  by rewrite (normalize_cond_eP1 hx0) /= hb.
- move=> o es b; t_xrbindP=> vs hvs hop.
  have -> :
    mapM (sem_pexpr true gd s) [seq normalize_cond_e i | i <- es] = ok vs.
  + exact: normalize_cond_eP2 hvs.
  by rewrite /= hop.
- move=> e1 e2 b; t_xrbindP=> lo x0 hx0 hlo sz x1 hx1 hsz <-.
  by rewrite (normalize_cond_eP1 hx0) /= hlo /= (normalize_cond_eP1 hx1) /= hsz.
move=> a1 ih1 a2 ih2 b; t_xrbindP=> b1 hb1 b2 hb2 <-.
by rewrite (ih1 _ hb1) /= (ih2 _ hb2).
Qed.

Let sim := st_rel (fun _ : unit => eq).
Notation st_eq := (sim tt).

Lemma normalize_cond_st_rel_eq d s1 s2 :
  sim d s1 s2 ->
  s1 = s2.
Proof. by case: s1 s2 => ??? [] ??? [] /= <- <- <-. Qed.

Definition check_es_normalize_cond (_ : unit) (es1 es2 : pexprs) (_ : unit) :=
  es2 = normalize_cond_es es1.

Definition check_lvals_normalize_cond (_ : unit) (xs1 xs2 : lvals) (_ : unit) :=
  xs2 = normalize_cond_lvals xs1.

Lemma check_esP_R_normalize_cond d es1 es2 d' :
  check_es_normalize_cond d es1 es2 d' ->
  forall s1 s2,
    sim d s1 s2 ->
    sim d' s1 s2.
Proof. by []. Qed.

Definition checker_normalize_cond : Checker_e sim :=
  {|
    check_es := check_es_normalize_cond;
    check_lvals := check_lvals_normalize_cond;
    check_esP_rel := check_esP_R_normalize_cond;
  |}.

Definition check_a_normalize_cond (_ : unit) (a1 a2 : eassert) (_ : unit) :=
  a2 = normalize_cond_eassert a1.

Lemma check_aP_R_normalize_cond d a1 a2 d' :
  check_a_normalize_cond d a1 a2 d' ->
  forall s1 s2,
    sim d s1 s2 ->
    sim d' s1 s2.
Proof. by []. Qed.

Definition checker_a_normalize_cond : Checker_a sim :=
  {|
    check_a := check_a_normalize_cond;
    check_aP_rel := check_aP_R_normalize_cond;
  |}.

Instance checker_normalize_condP : Checker_eq p p' checker_normalize_cond.
Proof using normalize_cond_ok.
rewrite -normalize_cond_ok.
constructor.
- move=> wdb1 wdb2 d es1 es2 d'.
  move=> /wdb_ok_eq <- -> s t v /normalize_cond_st_rel_eq <- hes.
  by exists v => //; apply: normalize_cond_eP2 hes.
move=> wdb1 wdb2 d xs1 xs2 d'.
move=> /wdb_ok_eq <- -> vs s t s' /normalize_cond_st_rel_eq <- hxs.
by exists s' => //; apply: normalize_cond_lvalsP hxs.
Qed.

Instance checker_a_normalize_condP : Checker_a_eq p p' checker_a_normalize_cond.
Proof using normalize_cond_ok.
rewrite -normalize_cond_ok; constructor.
move=> d a1 a2 d' -> s t b /normalize_cond_st_rel_eq <- ha.
by exists b => //; apply: normalize_cond_eassertP ha.
Qed.

#[local] Hint Resolve checker_normalize_condP checker_a_normalize_condP : core.

Let Pi (i : instr) :=
  wequiv_rec p p' ev ev eq_spec st_eq [::i] [:: normalize_cond_ii i] st_eq.
Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).
Let Pc (c : cmd) :=
  wequiv_rec p p' ev ev eq_spec st_eq c (normalize_cond_c c) st_eq.

Lemma normalize_cond_cP c : Pc c.
Proof using E Pc Pi Pi_r asm_op dc ep ev normalize_cond_ok p p' rE0 sip
  spp syscall_state wE wsw.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
- by apply wequiv_nil.
- by move=> i c hi hc; apply wequiv_cons with st_eq.
- by move=> >; apply wequiv_assgn_rel_eq with checker_normalize_cond tt.
- by move=> >; apply wequiv_opn_rel_eq with checker_normalize_cond tt.
- move=> >.
  apply wequiv_syscall_rel_eq_core with checker_normalize_cond tt => //.
  by move=> > <- ->; eauto.
- move=> a ii.
  apply wequiv_assert_rel_eq with checker_a_normalize_cond.
  + exact: checker_a_normalize_condP.
  + exact: id.
  by case: a.
- move=> > hc1 hc2 ii.
  by apply wequiv_if_rel_eq with checker_normalize_cond tt tt tt.
- move=> > hc >.
  by apply wequiv_for_rel_eq with checker_normalize_cond tt tt.
- move=> > hc hc' >.
  by apply wequiv_while_rel_eq with checker_normalize_cond tt.
move=> >.
apply wequiv_call_rel_eq with checker_normalize_cond tt => //.
move=> ?? <-; exact/wequiv_fun_rec.
Qed.

Lemma get_fundef_normalize_cond fn :
  get_fundef (p_funcs (normalize_cond_prog p)) fn =
    omap normalize_cond_fd (get_fundef (p_funcs p) fn).
Proof.
rewrite /get_fundef /normalize_cond_prog /=.
by elim: (p_funcs p) => [|[fn' fd'] pfuns ih] //=; case: eqP.
Qed.

Lemma normalize_cond_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using normalize_cond_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
exists (normalize_cond_fd fd).
- by rewrite -normalize_cond_ok get_fundef_normalize_cond hget.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -normalize_cond_ok.
exists st_eq, st_eq; split=> //; first exact: normalize_cond_cP.
by move=> ? _ fr /normalize_cond_st_rel_eq <- hfin; exists fr.
Qed.

End NORMALIZE_COND_PROOF.
