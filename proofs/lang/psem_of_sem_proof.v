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
  end.

  Lemma sem_pexpr_s_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    case: hs => ??.
    by apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP => *;
      rewrite -/(sem_pexprs _ _); sem_pexpr_sim_t.
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

Lemma write_lval_sim s1 x v s2 s1' :
  estate_sim s1 s1' →
  sem.write_lval gd x v s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ psem.write_lval gd x v s1' = ok s2'.
Proof.
case => hm hvm; case: x => /=.
- move => _ ty; rewrite /sem.write_none /psem.write_none; apply: on_vuP.
  + move => w hw <- {s2}; exists s1'; split; first by [].
    by case /exec_val_simE: (of_val_sim hw) => v' [-> _].
  case: is_sboolP => // ?;subst ty.
  move /of_val_undef_sim => /exec_val_simE /= -> /= [<-].
  by exists s1'.
- move => x; exact: write_var_sim.
- move => sz x e; t_xrbindP => ? ?;
    rewrite hm (get_var_sim hvm) => -> /= -> ?? /(sem_pexpr_sim (conj hm hvm))
        -> /= -> ? -> ? /= -> <- /=.
  by eexists; split; split.
move => ws x e; rewrite /sem.on_arr_var /psem.on_arr_var (get_var_sim hvm).
t_xrbindP => t -> /=.
case: t => // n t; t_xrbindP => ?? /(sem_pexpr_sim (conj hm hvm)) -> /= -> ? -> /= ? -> ? /(set_var_sim hvm).
case => vm' [] h /= -> <- /=.
by eexists; split; split.
Qed.

Corollary write_lvals_sim s1 xs vs s2 s1' :
  estate_sim s1 s1' →
  sem.write_lvals gd s1 xs vs = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ psem.write_lvals gd s1' xs vs = ok s2'.
Proof.
elim: xs vs s1 s1'.
- by case => // ? ? h [<-]; eauto.
move => x xs ih [] // v vs s1 s1' h /=; apply: rbindP => s' /(write_lval_sim h) [s2'] [h'] ->.
exact: (ih _ _ _ h').
Qed.

Let Pc s1 c s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem p s1' c s2'.

Let Pi_r s1 i s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_i p s1' i s2'.

Let Pi s1 i s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_I p s1' i s2'.

Let Pfor x ws s1 c s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ psem.sem_for p x ws s1' c s2'.

Let Pfun := psem.sem_call p.

Lemma psem_call m fn va m' vr :
  sem.sem_call p m fn va m' vr →
  psem.sem_call p m fn va m' vr.
Proof.
apply: (@sem.sem_call_Ind p Pc Pi_r Pi Pfor Pfun) => {m fn va m' vr}.
- by move => s s' hss'; exists s'; split; first exact: hss'; constructor.
- move => s1 s2 s3 [ii i] c [] {ii i s1 s2} ii i s1 s2 _ ihi _ ihc s1' hss'1.
  case: (ihi s1' hss'1) => s2' [hss'2 hi].
  case: (ihc s2' hss'2) => s3' [hss'3 hc].
  by exists s3'; split; first exact: hss'3; econstructor; eauto.
- move => ii i s1 s2 _ ih s1' hss'1.
  case: (ih s1' hss'1) => s2' [hss'2 hi].
  by exists s2'; split; first exact: hss'2; constructor.
- move => s1 s2 x tg ty e v1 v2 hv1 hv2 hw s1' hss'1.
  have hv1' := sem_pexpr_sim hss'1 hv1.
  case: (write_lval_sim hss'1 hw) => s2' [hss'2 hw'].
  exists s2'; split; first exact: hss'2.
  by econstructor; eauto.
- move => s1 s2 tg op xs es; rewrite /sem.sem_sopn; t_xrbindP => vr va /sem_pexprs_sim hva hvr /write_lvals_sim hw s1' hss'1.
  case: (hw _ hss'1) => s2' [hss'2 hw']; exists s2'; split; first exact: hss'2.
  econstructor; eauto.
  by rewrite /sem_sopn (hva) //= hvr.
- move => s1 s2 e th el /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hth].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 e th el /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hel].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 s3 s4 a c e c' _ ih /sem_pexpr_sim he _ ih' _ ihwh s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  case: (ih' _ hss'2) => s3' [hss'3 hcc'].
  case: (ihwh _ hss'3) => s4' [hss'4 hwh].
  exists s4'; split; first exact: hss'4.
  once (econstructor; eauto; fail).
- move => s1 s2 a c e c' _ ih /sem_pexpr_sim he s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 x d lo hi c vlo vhi /sem_pexpr_sim hlo /sem_pexpr_sim hhi _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  once (econstructor; eauto; fail).
- by move => s1 x c s1' hss'1; exists s1'; split => //; constructor.
- move => s1 s2 s3 s4 x w ws c /write_var_sim hw _ ih _ ih' s1' hss'1.
  case: (hw _ hss'1) => s2' [hss'2 hw'].
  case: (ih _ hss'2) => s3' [hss'3 hc].
  case: (ih' _ hss'3) => s4' [hss'4 hf].
  exists s4'; split; first exact: hss'4.
  econstructor; eauto.
- move => s1 m2 s2 ii xs fn args vargs vs /sem_pexprs_sim hargs _ ih /write_lvals_sim hres s1' [hm hvm].
  rewrite hm in ih.
  case: (hres {| emem := m2 ; evm := evm s1' |} (conj erefl hvm)) => s2' [hss'2 hw].
  exists s2'; split; first exact: hss'2.
  econstructor; eauto.
  by apply: hargs; split.
move => m m2 fn fd va va' s1 vm2 vr vr' hfn htyin /write_vars_sim => /(_ {| emem := m |} (conj erefl vmap0_sim)).
case => s1' [hss'1 hargs] _ /(_ _ hss'1) [[m2' vm2']] [] [] /= <- {m2'} hvm ih.
rewrite (mapM_ext (λ x : var_i, get_var_sim hvm x) erefl) => hres htyout.
econstructor; eauto.
Qed.

End PROOF.
