Require Import psem.
Import Utf8.
Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.
Context (p: prog).
Notation gd := (p_globs p).

Definition word_sim (s: wsize) (w: word s) (w': pword s) : Prop :=
  w' = pword_of_word w.

Definition val_sim t : sem_t t → psem_t t → Prop :=
  match t with
  | sbool => eq
  | sint => eq
  | sarr n => eq
  | sword s => @word_sim s
  end.

Definition exec_val_sim t (v: exec (sem_t t)) (v': exec (psem_t t)) : Prop :=
  match v, v' with
  | Ok x, Ok x' => val_sim x x'
  | Error e, Error e' => e = e'
  | _, _ => False
  end.

Lemma exec_val_simE t v v' :
  @exec_val_sim t v v' →
  match v with
  | Ok x => ∃ x', v' = ok x' ∧ val_sim x x'
  | Error e => v' = Error e
  end.
Proof.
case: v v' => //.
- move => x [] //; eauto.
by move => e [] // e' ->.
Qed.

Definition vmap_sim (vm: sem.vmap) (vm': psem.vmap) : Prop :=
  (∀ x : var, exec_val_sim vm.[x] vm'.[x])%vmap.

Lemma vmap0_sim : vmap_sim sem.vmap0 psem.vmap0.
Proof. by move => x; rewrite !Fv.get0; case: (vtype _). Qed.

Definition estate_sim (e: sem.estate) (e': psem.estate) : Prop :=
  sem.emem e = psem.emem e' ∧ vmap_sim (sem.evm e) (psem.evm e').

Lemma val_sim_to_val t x x' :
  @val_sim t x x' →
  to_val x = pto_val x'.
Proof.
by case: t x x'; (move => ?? -> || move => ??? -> || move => ???? ->).
Qed.

Lemma of_val_sim t x v :
  of_val t x = ok v →
  exec_val_sim (ok v) (pof_val t x).
Proof.
move => h; rewrite -h; move: h.
case: t v => [ | | n | sz ]; case: x => //; try by case.
- move => n' t' t /=.
  by rewrite /WArray.cast /WArray.inject Z.ltb_antisym;case:ZleP.
- move => sz' w' /= w h.
  rewrite h /=.
  case: (truncate_wordP h) => {h} hle ?; subst w.
  case: Sumbool.sumbool_of_bool => // hle'.
  have ? := cmp_le_antisym hle hle' => {hle}; subst.
  by rewrite zero_extend_u /word_sim /pword_of_word (Eqdep_dec.UIP_dec Bool.bool_dec (cmp_le_refl sz')).
Qed.

Lemma of_val_undef_sim x :
  of_val sbool x = undef_error →
  exec_val_sim undef_error (pof_val sbool x).
Proof. by case: x => //= -[]. Qed.

Lemma get_var_sim vm vm' :
  vmap_sim vm vm' →
  ∀ x, sem.get_var vm x = psem.get_var vm' x.
Proof.
move => h x; rewrite /sem.get_var /psem.get_var.
case: (vm.[x])%vmap (h x) => a /exec_val_simE.
- by case => a' [] -> ha /=; rewrite (val_sim_to_val ha).
by move => ->.
Qed.

Lemma vmap_set_sim vm vm' x v v' :
  vmap_sim vm vm' →
  exec_val_sim v v' →
  (vmap_sim vm.[x <- v] vm'.[x <- v'])%vmap.
Proof.
move => hvm hv y; case: (x =P y).
- by move => ?; subst; rewrite !Fv.setP_eq.
by move => /eqP ne; rewrite !(Fv.setP_neq _ _ ne).
Qed.

Lemma set_var_sim vm1 vm1' x v vm2 :
  vmap_sim vm1 vm1' →
  sem.set_var vm1 x v = ok vm2 →
  ∃ vm2',
    vmap_sim vm2 vm2' ∧
    psem.set_var vm1' x v = ok vm2'.
Proof.
move => h; rewrite /sem.set_var /psem.set_var; apply: on_vuP.
- move => t ht <- {vm2}.
  case/exec_val_simE: (of_val_sim ht) => t' [-> htt'] /=.
  eexists; split; last reflexivity.
  exact: vmap_set_sim.
case: x => xt x;case: is_sboolP => //= ?;subst xt.
move => /of_val_undef_sim /exec_val_simE /= -> [<-] /=.
eexists; split; last reflexivity.
by apply: vmap_set_sim.
Qed.

Section SEM_PEXPR_SIM.

  Context (s: sem.estate) (s': estate) (hs: estate_sim s s').

  Let P e : Prop :=
    ∀ v,
      sem.sem_pexpr gd s e = ok v →
      psem.sem_pexpr gd s' e = ok v.

  Let Q es : Prop :=
    ∀ vs,
      sem.sem_pexprs gd s es = ok vs →
      psem.sem_pexprs gd s' es = ok vs.

  Local Ltac sem_pexpr_sim_t :=
  repeat match goal with
  | _ : ?a = ?b |- _ => subst a || subst b
  | h : to_int _ = ok _ |- _ => apply of_val_int in h
  | h : ∀ x, _ → _ , k : _ |- _ => specialize (h _ k) => {k}
  | h : ?p = ok _ |- _ => rewrite h /= => {h}
  | hm: sem.emem _ = _, h : context[sem.emem _] |- _ => rewrite hm in h
  | hvm: vmap_sim ?vm _, h : context[ sem.get_var ?vm _] |- _ => rewrite (get_var_sim hvm) in h
  | h : sem.on_arr_var _ _ _ = ok _ |- _ => unfold sem.on_arr_var in h; unfold psem.on_arr_var
  | h : (if _ then _ else _) = ok _ |- _ =>
    move: h; case: eqP => // ->; rewrite eqxx
  | h : Let x := _ in _ = ok _ |- _ => move: h; t_xrbindP => *
  | h : match ?x with _ => _ end = ok _ |- _ => move: h; case: x => // *
  | |- _ = _ => auto
  end.

  Lemma sem_pexpr_s_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    case: hs => hvm Hvm.
    apply: pexprs_ind_pair; subst P Q; split => //=.
    + t_xrbindP=> *;sem_pexpr_sim_t.
    + t_xrbindP=> *;sem_pexpr_sim_t.
    + move=> sz x e H v. apply sem.on_arr_varP => n t Htx;rewrite /on_arr_var => Hg.
      move: (get_var_sim Hvm). move=> Hg'. move: (Hg' x) => Hg''. t_xrbindP.
      move=> y Hsem h0 Hint h2 Hw <-. rewrite -Hg'' /=. rewrite Hg /=.
      move: (H y Hsem) => -> /=. rewrite Hint /=. by rewrite Hw /=.
    + t_xrbindP=> *;sem_pexpr_sim_t.
    + t_xrbindP=> *;sem_pexpr_sim_t.
    + t_xrbindP=> *;sem_pexpr_sim_t.
    + rewrite /sem.sem_pexprs. move=> op es H.
      t_xrbindP.  move=> [hv hl] y Hm.
      move: (H y Hm). rewrite /sem_pexprs. move=> -> /=.
      by move=> h1 -> <- /=.
    t_xrbindP=> *;sem_pexpr_sim_t.
  Qed.

  End SEM_PEXPR_SIM.

Definition sem_pexpr_sim s e v s' h :=
  (@sem_pexpr_s_sim s s' h).1 e v.
Definition sem_pexprs_sim s es vs s' h :=
  (@sem_pexpr_s_sim s s' h).2 es vs.

Lemma write_var_sim s1 x v s2 s1' :
  estate_sim s1 s1' →
  sem.write_var x v s1 = ok s2 →
  ∃ s2' : estate, estate_sim s2 s2' ∧ psem.write_var x v s1' = ok s2'.
Proof.
case => hm hvm; rewrite /sem.write_var /psem.write_var; t_xrbindP => vm hw <- {s2}.
case: (set_var_sim hvm hw) => vm' [hvm' ->].
by eexists; split; split.
Qed.

Corollary write_vars_sim s1 xs vs s2 s1' :
  estate_sim s1 s1' →
  sem.write_vars xs vs s1 = ok s2 →
  ∃ s2' : estate, estate_sim s2 s2' ∧ psem.write_vars xs vs s1' = ok s2'.
Proof.
elim: xs vs s1 s1' s2.
- by case => // s1 s1' s2 h [<-]; exists s1'.
by move => x xs ih [] // v vs s1 s1' s3 hss'1 /=; apply: rbindP => s2 /(write_var_sim hss'1) [s2'] [hss'2 ->] /(ih _ _ _ _ hss'2).
Qed.

Lemma write_lval_sim s1 x v s2 l2 s1' :
  estate_sim s1 s1' →
  sem.write_lval gd x v s1 = ok (s2, l2) →
  ∃ s2', estate_sim s2 s2' ∧ psem.write_lval gd x v s1' = ok (s2', l2).
Proof.
case => hm hvm; case: x => /=.
- move => _ ty; rewrite /sem.write_none /psem.write_none; t_xrbindP. move=> y. apply: on_vuP.
  + move => w hw <- <- <-; exists s1'; split; first by [].
    by case /exec_val_simE: (of_val_sim hw) => v' [-> _].
  case: is_sboolP => // ?;subst ty.
  move /of_val_undef_sim => /exec_val_simE /= -> /= [<-].
  move => <- <-.
  by exists s1'.
- move=> x. t_xrbindP. move=> y H <- <-.
  move: (write_var_sim). move=> Hw. move: (Hw s1 x v y s1' (conj hm hvm) H) => [] s2' [] Hvm -> /=.
  by exists s2'.
- move => sz x e; t_xrbindP.
  move=> y h Hg H2 h2 Hs h4 H4 h6 Hw h8 Hm <- <-.
  move: (get_var_sim hvm x) => H. rewrite H in Hg. rewrite Hg /= H2 /=.
  move: (sem_pexpr_sim). move=> Hsem. move: (Hsem s1 e h2 s1' (conj hm hvm) Hs) => -> /=.
  rewrite H4 /=. rewrite Hw /=. rewrite -hm Hm /=. exists {| emem := h8; evm := evm s1' |}. split.
  by rewrite /estate_sim. auto.
move => ws x e; rewrite /sem.on_arr_var /psem.on_arr_var (get_var_sim hvm).
t_xrbindP => t -> /=.
case: t => // n t. t_xrbindP.
move=> y Hs h0 Hi h2 Hw h4 Ha h6 Hs' <- <-.
move: (sem_pexpr_sim) => H. move: (H s1 e y s1' (conj hm hvm)). move=> -> /=. rewrite Hi Hw /=.
rewrite Ha /=. move: (set_var_sim hvm Hs') => [] h7 [] H2 H3. rewrite H3 /=.
exists {| emem := emem s1'; evm := h7 |}. split. rewrite /estate_sim. split; auto.
auto. auto.
Qed.

Corollary write_lvals_sim s1 xs vs s2 l2 s1' :
  estate_sim s1 s1' →
  sem.write_lvals gd s1 xs vs = ok (s2, l2) →
  ∃ s2', estate_sim s2 s2' ∧ psem.write_lvals gd s1' xs vs = ok (s2', l2).
Proof.
rewrite /write_lvals. rewrite /sem.write_lvals.
elim: xs vs s1 s1' s2 l2.
- case => // s1 s1' s2 l2 h [<-] <-. exists s1'. split. by auto. auto.
move => x xs ih [] // v vs s1 s1' s2 l2 h /=. t_xrbindP.
move=> [s' l'] /(write_lval_sim h) [] s2' [] h' -> /= [s2'' l2''] h'' /= <- <-.
move: (ih vs s' s2' s2'' l2'' h' h''). move=> [] s'' [] h1 h1'. exists s''.
by split=> //; rewrite h1' /=.
Qed.

Let Pc s1 c lc s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem p s1' c lc s2'.

Let Pi_r s1 i li s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_i p s1' i li s2'.

Let Pi s1 i li s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_I p s1' i li s2'.

Let Pfor x ws s1 c lc s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_for p x ws s1' c lc s2'.

Let Pfun := psem.sem_call p.

Lemma sem_range_sim r s1 v l s1' :
  estate_sim s1 s1' →
  sem.sem_range p s1 r = ok (v, l) →
  psem.sem_range p s1' r = ok (v, l).
Proof.
 move=> Hvm. elim: r v l. move=> [d p1] p2 v1 le /=.
 t_xrbindP. move=> y Hs h0 Hint y' Hs' h4 Hint' <- <-.
 move: (sem_pexpr_sim). move=> H. move: (H s1 p1 y s1' Hvm Hs) => -> /=.
 rewrite Hint /=. move: (sem_pexpr_sim). move=> H'. move: (H' s1 p2 y' s1' Hvm Hs') => -> /=.
 by rewrite Hint' /=.
Qed.


Lemma psem_call m fn va m' l vr :
  sem.sem_call p m fn va l m' vr →
  psem.sem_call p m fn va l m' vr.
Proof.
apply: (@sem.sem_call_Ind p Pc Pi_r Pi Pfor Pfun) => {m fn va l m' vr}.
- by move => s s' hss'; exists s'; split; first exact: hss'; constructor.
- move => s1 s2 s3 [ii i] c li lc [] {ii i s1 s2 li} ii i s1 s2 li _ ihi _ ihc s1' hss'1.
  case: (ihi s1' hss'1) => s2' [hss'2 hi].
  case: (ihc s2' hss'2) => s3' [hss'3 hc].
  by exists s3'; split; first exact: hss'3; econstructor; eauto.
- move => ii i s1 s2 li _ ih s1' hss'1.
  case: (ih s1' hss'1) => s2' [hss'2 hi].
  by exists s2'; split; first exact: hss'2; constructor.
- move => s1 s2 x tg ty e v1 v2 le lw hv1 hv2 hw s1' hss'1.
  have hv1' := sem_pexpr_sim hss'1 hv1.
  case: (write_lval_sim hss'1 hw) => s2' [hss'2 hw'].
  exists s2'; split; first exact: hss'2.
  by econstructor; eauto.
- move => s1 s2 tg op xs es lo. rewrite /sem.sem_sopn. rewrite /sem.sem_pexprs.
  t_xrbindP. move=> y Hm h2 Hex [hv hl] Hw <- /= <-.
  move=> s1' H.
  move: (sem_pexprs_sim) => Hm'. rewrite /sem.sem_pexprs in Hm'.
  move: (Hm' s1 es y s1' H Hm) => Hmm.
  move: (write_lvals_sim) => Hw'. move: (Hw' s1 xs h2 hv hl s1' H Hw) => [] s2' [] Hvm' Hww. exists s2'.
  split. auto.
  constructor. rewrite /sem_sopn. rewrite /sem_pexprs.
  rewrite /sem_pexprs in Hmm. rewrite Hmm /=. rewrite Hex /=.
  by rewrite Hww /=.
- move => s1 s2 e th el le lc /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hth].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 e th el le lc /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hel].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 s3 s4 a c e c' lc le lc' li  _ ih /sem_pexpr_sim he _ ih' _ ihwh s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  case: (ih' _ hss'2) => s3' [hss'3 hcc'].
  case: (ihwh _ hss'3) => s4' [hss'4 hwh].
  exists s4'; split; first exact: hss'4.
  once (econstructor; eauto; fail).
- move => s1 s2 a c e c' lc le _ ih /sem_pexpr_sim he s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 i r wr c lr lf hhi _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  move: (sem_range_sim hss'1 hhi) => hhii. apply Efor with wr; auto.
- by move => s1 x c s1' hss'1; exists s1'; split => //; constructor.
- move => s1 s2 s3 s4 x w ws c lc lf /write_var_sim hw _ ih _ ih' s1' hss'1.
  case: (hw _ hss'1) => s2' [hss'2 hw'].
  case: (ih _ hss'2) => s3' [hss'3 hc].
  case: (ih' _ hss'3) => s4' [hss'4 hf].
  exists s4'; split; first exact: hss'4.
  econstructor; eauto.
- move => s1 m2 s2 ii xs fn args vargs vs lf lw /sem_pexprs_sim hargs _ ih /write_lvals_sim hres s1' [hm hvm].
  rewrite hm in ih.
  case: (hres {| emem := m2 ; evm := evm s1' |} (conj erefl hvm)) => s2' [hss'2 hw].
  exists s2'; split; first exact: hss'2.
  econstructor; eauto.
  by apply: hargs; split.
move => m m2 fn fd va va' s1 vm2 vr vr' lc hfn htyin /write_vars_sim => /(_ {| emem := m |} (conj erefl vmap0_sim)).
case => s1' [hss'1 hargs] _ /(_ _ hss'1) [[m2' vm2']] [] [] /= <- {m2'} hvm ih.
rewrite (mapM_ext (λ x : var_i, get_var_sim hvm x) erefl) => hres htyout.
econstructor; eauto.
Qed.

End PROOF.
