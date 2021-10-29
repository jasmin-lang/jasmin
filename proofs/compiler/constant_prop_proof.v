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
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem.
Require Export compiler_util constant_prop.

Import Utf8 ZArith Morphisms Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.

Local Notation cpm := (Mvar.t const_v).

(* ** proofs
 * -------------------------------------------------------------------- *)

Section GLOB_DEFS.

Context {LO: LeakOp}.
Context (gd: glob_decls).

Variable stk: pointer.

Definition eqok_w (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v -> sem_pexpr gd st e2 = ok v.

Definition eqok (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v ->
    exists v', sem_pexpr gd st e2 = ok v' /\ value_uincl v.1 v'.1 /\ v.2 = v'.2.

Lemma eqok_weaken e1 e2 st : eqok_w e1 e2 st -> eqok e1 e2 st.
Proof. by move=> h v /h h';exists v. Qed.

Notation "e1 '=[' st ']' e2" := (eqok e1 e2 st)
 (at level 70, e2 at next level, no associativity,
  format "'[hv ' e1  =[ st ]  '/'  e2 ']'").

Definition eeq_w (e1 e2:pexpr) := forall rho, eqok_w e1 e2 rho.
Definition eeq (e1 e2:pexpr) := forall rho, e1 =[rho] e2.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).


Lemma eeq_w_refl : Reflexive (@eeq_w).
Proof. by move=> ???;eauto. Qed.

Lemma eeq_refl : Reflexive (@eeq).
Proof. by move=> ??? ->;eauto. Qed.

Hint Resolve eeq_refl eeq_w_refl : core.

Lemma eeq_weaken e1 e2 : eeq_w e1 e2 -> e1 =E e2.
Proof. by move=> h ?;apply eqok_weaken;apply h. Qed.

Definition trans_sem t (vl:value * leak_e) := (vl.1, leak_E stk t vl.2).

Definition trans_sem_estate t (vl:estate * leak_e) := (vl.1, leak_E stk t vl.2).

Definition trans_sem_estates t (vl: estate* seq leak_e) := (vl.1, leak_E stk (LT_map t) (LSub (vl.2))).

Lemma sint_of_wordPl sz s e v l:
let e' := (sint_of_word sz e).1 in
let t := (sint_of_word sz e).2 in
sem_pexpr gd s (Papp1 (Oint_of_word sz) e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sint_of_word. rewrite /trans_sem /=.
case: (is_wconst _ _) (@is_wconstP LO gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [ve le] He /= Hw. rewrite /= /sem_sop1 /=.
  t_xrbindP. move=> [yv yl] He' h0 h1 /= Hw1 <- lo hlo <- Hle.
  exists (wunsigned w). split. auto.
  rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw1 in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho lo Hlo <- /= Hl.
  exists vo. rewrite He /=. rewrite Ho Hlo /=.
  split. by rewrite Hl /=. auto.
Qed.

Lemma ssign_extendPl sz sz' s e v l:
let e' := (ssign_extend sz sz' e).1 in
let t := (ssign_extend sz sz' e).2 in
sem_pexpr gd s (Papp1 (Osignext sz sz') e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /ssign_extend. rewrite /trans_sem.
case: (is_wconst _ _) (@is_wconstP LO gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v /= ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 /= Hw Hv lo /= Hlo <- <- /=. rewrite wrepr_unsigned.
  exists (Vword (sign_extend sz w)). split. auto. rewrite /leak_sop1 in Hlo.
  move: Hlo. t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  rewrite -Hv. rewrite ok_v in He. case: He => He1 _. rewrite He1 in ok_w.
  rewrite ok_w in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho le Hle <- /= Hl /=.
  exists vo. rewrite He /=.
  rewrite Ho /=. by rewrite Hle /= Hl.
Qed.

Lemma szero_extendPl sz sz' s e v l:
let e' := (szero_extend sz sz' e).1 in
let t := (szero_extend sz sz' e).2 in
sem_pexpr gd s (Papp1 (Ozeroext sz sz') e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /szero_extend. rewrite /trans_sem.
case: (is_wconst _ _) (@is_wconstP LO gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 Hw Hv le Hlo Hvv <- /=. rewrite wrepr_unsigned.
  exists (Vword (zero_extend sz w)). split. auto. rewrite Hvv in Hv.
  rewrite /leak_sop1 in Hlo.
  move: Hlo. t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  subst. rewrite ok_v in He. case: He => He1 _. rewrite He1 in ok_w.
  rewrite ok_w in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho le Hle <- /= <- /=.
  exists vo. rewrite He /=.
  by rewrite Ho Hle /=.
Qed.

Lemma snot_boolPl s e v l:
let e' := (snot_bool e).1 in
let t := (snot_bool e).2 in
sem_pexpr gd s (Papp1 Onot e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /snot_bool. rewrite /trans_sem.
case: e=> //= ;try auto.
+ move=> b [] <- _. by exists (~~b).
+ move=> x. t_xrbindP.
  move=> [yv yl] h Hg [] Hv1 Hv2. rewrite /sem_sop1 /=.
  t_xrbindP. move=> h0 y Hb Hv' le Hlo Hv'' Hl. rewrite Hg /=. rewrite -Hv1 in Hb.
  rewrite Hb /=. subst. rewrite Hlo /=. by exists (~~y).
+ move=> g. t_xrbindP.
  move=> [yv yl] vg Hg [] <- Heyl. rewrite /sem_sop1 /=.
  t_xrbindP. move=> vb b Hb Heb le Hlo Hv Hl. subst.
  rewrite Hg /= Hb /= Hlo /=. by exists (~~ b).
+ move=> w v0 e. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi w' Ha Hv Hl. 
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> vb b Hb /= Heb le Hlo <- Hel /=. rewrite He /= Hi /= Ha /=; subst.
  exists (~~b). split. by inversion Hb. by auto.
+ move=> w x e. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh Hhv Hyl.
  rewrite Hg /=. rewrite Hp /=. rewrite He /=. rewrite Hp' /=.
  rewrite Hr /=. case: He' => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. move=> _ _. exists (~~ b). by inversion Hb.
+ move=> s0 e. t_xrbindP.
  move=> h [yv yl] He /= h1 Ho les Hlo <-. rewrite /sem_sop1 /=.
  t_xrbindP => h0 y /to_boolI h' h2 h3 h4 h5 h6; subst.
  case hop: (if s0 is Onot then false else true).
  exists (~~ y). case: s0 hop Ho Hlo => //=.
  + rewrite He /=. move=> w ht -> /= -> /=.
    rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  + rewrite He /=. move=> w ht -> -> /=. 
    rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  + rewrite He /=. move=> w w0 ht -> -> /=. 
    rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  + rewrite He /=. move=> o ht _ -> -> /=. rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  + rewrite He /=. move=> sz _ -> -> /=. rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  + rewrite He /=. move=> sz _ -> -> /=. rewrite /leak_sop1 in h4. move: h4. 
    t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
  exists (~~y). case: s0 hop Ho Hlo => //=.
  rewrite He /=. move=> hf ho' hlo. rewrite /sem_sop1 in ho'. move: ho'.
  t_xrbindP. move=> y0 /to_boolI -> <-. split=> //. by rewrite negbK.
+ move=> s0 e e0. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 /= Hs2 /= le Hlo Hev v1 Hs1 le' Hlo' <- Hl'.
  rewrite He /= He0 /= Hs2 /= Hlo /=. rewrite -Hev /= in Hs1.
  rewrite Hs1 /=. rewrite -Hev /= in Hl' Hlo'. rewrite -Hl' Hlo' /=.
  by exists v1.
+ move=> o l0. t_xrbindP. move=> [yv yl] h Hm h1 H le Hlo.
  rewrite /sem_sop1 /=. t_xrbindP. move=> [] <- <- /=.
  move=> h0 y Hb Hh le' Hlo' <- <- /=. rewrite Hm /=.
  rewrite H /= Hlo /= Hb /= Hlo' /=; subst. by exists (~~ y).
+ move=> ty e e0 e1. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh le Hlo <- Hl; subst.
  rewrite He /= Hb /= He0 /= He1 /= Ht /= Ht1 /= Hb' /= Hlo /=. 
  by exists (~~ y2).
Qed.

Lemma snot_wPl sz s e v l:
let e' := (snot_w sz e).1 in
let t := (snot_w sz e).2 in
sem_pexpr gd s (Papp1 (Olnot sz) e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /snot_w. rewrite /trans_sem.
case: is_wconst (@is_wconstP LO gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [yv yl] He Hw /=. rewrite /sem_sop1 /= wrepr_unsigned.
  t_xrbindP. move=> [yv' yl'] He'. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' <- le Hlo <- Hhl; subst.
  exists (Vword (wnot w)). 
  rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw in Hw'; subst. case: Hw' => ->.
  split=> //. rewrite /leak_sop1 in Hlo. move: Hlo. 
  t_xrbindP=> //= w' hw'. rewrite /leak_sop1_typed /=. by move=> [] <- /=.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- le Hlo <- <-. rewrite He /= Hw /= Hlo /=.
  by exists (Vword (wnot y)).
Qed.

Lemma sneg_intPl s e v l:
let e' := (sneg_int e).1 in
let t := (sneg_int e).2 in
sem_pexpr gd s (Papp1 (Oneg Op_int) e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. case: e => //.
+ move=> z /= He /=. exists ((- z)%Z).
  by case: He => <- _.
+ move=> x /=. t_xrbindP.
  move=> [yv yl] h Hg Hh. rewrite /sem_sop1 /=.
  t_xrbindP. move=> h0 y Hi <- le Hlo <- <-. rewrite Hg /=.
  case: Hh => -> <-. rewrite Hi /= Hlo /=. by exists (-y)%Z.
+ move=> g /=. t_xrbindP.
  move=> [yv yl] h Hg h2. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hi <- le Hlo <- <-; subst. rewrite Hg /=.
  case: h2 => h2v <-. rewrite h2v Hi /= Hlo /=. by exists (-y)%Z.
+ move=> sz x e /=. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi h2 Ha Hv Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hi' <- le Hlo <- Hl'. rewrite He /= Hi /= Ha /=. 
  rewrite -Hv /= in Hi'. by inversion Hi'.
+ move=> w x e /=. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh le Hlo Hhv Hyl; subst.
  rewrite Hg /= Hp /= He /= Hp' /= Hr /=. case: He' => He1' He2'. rewrite -He1' in Hb.
  by inversion Hb.
+ move => op e /=; t_xrbindP => [yv yl] he vo hop le hlo <-.
  rewrite /sem_sop1 /=; t_xrbindP => h y /to_intI h1 <- le' hlo' <- <-; subst.
  * have H : sem_pexpr gd s (Papp1 (Oneg Op_int) (Papp1 op e)) = 
    ok (Vint (- y)%Z, leak_E stk LT_id  (LSub [:: LSub [:: yl.2; le]; le'])). 
  rewrite /= he /= hop /= hlo /=. rewrite /leak_sop1 in hlo'.
  move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  case k: (if op is Oneg Op_int then false else true).
  exists (-y)%Z. case: (op) hop hlo => //=. 
  + rewrite he /=. move=> w -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w w0 -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w w' -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  + move=> o. case: o=> //=. rewrite he /=. rewrite /sem_sop1 /=. t_xrbindP.
    move=> y0 /to_intI hi /= <- hlo; subst. split=> //.
    rewrite Z.opp_involutive -hi /=. by case: (yl).
  + rewrite he /=. move=> w -> -> /=. rewrite /leak_sop1 in hlo'.
    move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-.
  case: (op) hop hlo hlo'=> //=. 
  + rewrite he /=. move=> w -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w w' -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w w' -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  + rewrite he /=. move=> w -> /= -> hlo' /=. exists (- y)%Z.
    rewrite /leak_sop1 in hlo'. move: hlo'. t_xrbindP=> sv /= [] _ /=. 
    rewrite /leak_sop1_typed /=. by move=> [] <-.
  move=> o. case: o=> //=.
  + rewrite /sem_sop1 /=. t_xrbindP. move=> y0 /to_intI hi /= h1 hlo hlo'. rewrite he /=. 
    exists yl.1. split=> //. by case: (yl). by rewrite -h1 hi Z.opp_involutive.
  rewrite he /=. move=> w -> -> hlo' /=. exists (- y)%Z.
  rewrite /leak_sop1 in hlo'.
  move: hlo'. t_xrbindP=> sv /= [] _ /=. rewrite /leak_sop1_typed /=. by move=> [] <-. 
+ move=> s0 e e0 /=. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 Hs2 le Hlo Hev v1 Hs1 le' Hlo' Hev' Hl'; subst.
  rewrite He /= He0 /= Hs2 /= Hlo /= Hs1 /= Hlo' /=. by exists v.
+ move=> o l0 /=. t_xrbindP. move=> [yv yl] h Hm h1 H le Hlo Hl; subst.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hb Hh le' Hlo' <- Hl'; subst. rewrite Hm /= H /= Hlo /=.
  case: Hl => Hl1 Hl2. rewrite -Hl1 in Hb Hlo'.
  rewrite Hb /= Hlo' /= -Hl2 /=. by exists (- y)%Z. 
+ move=> ty e e0 e1 /=. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh le Hlo <- Hl; subst. 
  rewrite He /= Hb /= He0 /= He1 /= Ht /= Ht1 /= Hb' /= Hlo /=.
  by exists (- y2)%Z.
Qed.

Lemma sneg_wPl sz s e v l:
let e' := (sneg_w sz e).1 in
let t := (sneg_w sz e).2 in
sem_pexpr gd s (Papp1 (Oneg (Op_w sz)) e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sneg_w. rewrite /trans_sem.
case: is_wconst (@is_wconstP LO gd s sz e).
+ move => w /(_ _ erefl) /=. t_xrbindP.
  move=> [yv yl] He Hw [yv' yl'] He'.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' <- le Hlo <- Hl; subst. rewrite wrepr_unsigned.
  exists (Vword (- w)). rewrite He in He'.
  case: He' => He1' He2'. rewrite He1' in Hw.
  rewrite Hw in Hw'. by case: Hw' => ->.
+ move=> _ /=. t_xrbindP. move=> [yv yl] He.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- le Hlo <- <-. rewrite He /= Hw /= Hlo /=.
  by exists (Vword (-y)).
Qed.

Lemma s_op1Pl s o e v l:
let e' := (s_op1 o e).1 in
let t := (s_op1 o e).2 in
sem_pexpr gd s (Papp1 o e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
case: o => [w|w|w w0|w w0||w|[|o]];
eauto using sint_of_wordPl, ssign_extendPl, szero_extendPl,
snot_boolPl, snot_wPl, sneg_intPl, sneg_wPl.
Qed.

(* * -------------------------------------------------------------------- *)

Lemma sandPl s e1 e2 v l:
let e' := (sand e1 e2).1 in
let t := (sand e1 e2).2 in
sem_pexpr gd s (Papp2 Oand e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sand. rewrite /trans_sem.
case: is_boolP => [b1 /=| {e1} e1].
+ t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop2 /=. case: b1.
  - t_xrbindP. move=> h y /to_boolI <- <- le Hlo <- <- /=.
    rewrite He /=. by exists yv.
  t_xrbindP. move=> h y /to_boolI H <- le Hlo <- <- /=. 
  by exists false.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y /to_boolI H <- le Hlo <- /= <- /=; subst. 
    rewrite He. exists y. split=> //. by rewrite andbT.
  t_xrbindP. move=> h y /to_boolI Hy <- le Hlo <- <- /=.
  exists false. split=> //. by rewrite andbF.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- le Hlo <- <-.
  rewrite He1 He2 /= Hb1 Hb2 /= Hlo /=. by exists (y && h1).
Qed.

Lemma sorPl s e1 e2 v l:
let e' := (sor e1 e2).1 in
let t := (sor e1 e2).2 in
sem_pexpr gd s (Papp2 Oor e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sor. rewrite /trans_sem.
case: is_boolP => [b1 /=| {e1} e1].
+ t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop2 /=. case: b1.
  - t_xrbindP. move=> h y /to_boolI H <- le Hlo <- <-.
    by exists true.
  t_xrbindP. move=> h y /to_boolI <- <- le Hlo <- <-. by exists yv.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y /to_boolI H <- le Hlo <- <- /=. exists true.
    split=> //. by rewrite orbT.
  t_xrbindP. move=> h y /to_boolI Hy <- le Hlo <- <- /=; subst.
  exists y. split=> //. by rewrite orbF.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- le Hlo <- <-.
  rewrite He1 He2 /= Hb1 Hb2 /= Hlo /=. by exists (y || h1).
Qed.

Lemma sadd_intPl s e1 e2 v l:
let e' := (sadd_int e1 e2).1 in
let t := (sadd_int e1 e2).2 in
sem_pexpr gd s (Papp2 (Oadd Op_int) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sadd_int. rewrite /trans_sem.
case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] //=.
+ t_xrbindP. move=> <- Hl. exists (n1 + n2)%Z.
  by split.
+ t_xrbindP. move=> [v2 l2] Hv2; rewrite /sem_sop2 /=.
  t_xrbindP. move=> h z2 /of_val_int /= H <- le Hlo <- <- /=; subst.
  case: eqP => [-> // | /= _]. by exists z2.
+ exists (n1 + z2)%Z.
  rewrite /sem_sop2 /= Hv2 /=. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= _ z [] hz [] <-. 
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h z /of_val_int /= H <- le Hlo <- <- /=; subst.
  case: eqP => [-> // | /= _]. exists z.
  by rewrite Z.add_0_r.
+ exists (z + n2)%Z.
  rewrite /sem_sop2 /= He /=. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= [] hz z' [] _ [] <-.
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> [yv' yl'] He2.
  move=> h1 y /of_val_int Hi h3 /of_val_int /= Hi' /=; subst.
  move=> <- le Hlo <- <- /=. rewrite He1 He2 /=. 
  rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. move=> sv /= _ z [] hz [] <-.
  by exists (y + h3)%Z. 
Qed.

Local Hint Resolve value_uincl_zero_ext : core.

Lemma sadd_wPl s sz e1 e2 v l:
let e' := (sadd_w sz e1 e2).1 in
let t := (sadd_w sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Oadd (Op_w sz)) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sadd_w. rewrite /trans_sem.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He' /= vo. 
  rewrite /sem_sop2 /=. t_xrbindP. move=>y Hw wsz Hw' <- le Hlo <- Hl /=; subst.
  rewrite wrepr_unsigned. exists (Vword (n1+n2)).
  have /= /(_ LO) := is_wconstP gd s h1; have /= /(_ LO) := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2.
  rewrite He2 in He'. case: He' => -> He2'. rewrite Hw' /=.
  move=> [] <-. rewrite He /=. move=> [yv1' yl1'] [] <- Hl'; subst.
  rewrite Hw /=. move=> [] <- /=. rewrite /leak_sop2 in Hlo.
  move: Hlo. by t_xrbindP=> st /= _ wsz' hw [] <-.
+ case: eqP => hz.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> [yv1 yl1] [] <- Hl -> h3 h4 [] <- h6 Hv; subst.
    move=> <- le Hlo <- Hl' /=. rewrite He2 /=.
    apply of_val_word in Hv. move: Hv. move=> [] sz' [] w' [] Hsz' -> ->.
    rewrite GRing.add0r /=.
    rewrite /word_uincl /zero_extend. exists (Vword w'). rewrite Hsz'.
    by rewrite -Hl' /=.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- le Hlo <- <- /=.
    rewrite He1 /=. exists (Vword (y + h3)).
    rewrite He2 /=. rewrite /sem_sop2 /=.
    rewrite Hw /=. by rewrite Hw' /= Hlo /=.
+ case: eqP => // hz /=. 
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have /= /(_ LO) := is_wconstP gd s h2.
    rewrite He' /=. move=> -> h y Hw'. move=> h3 [] <- <- le Hlo <- <- /=.
    rewrite He /=. exists yv.
    apply of_val_word in Hw'. move: Hw'. move=> [] sz' [] x0 [] Hsz -> ->.
    rewrite hz /=. rewrite GRing.addr0. rewrite /word_uincl /zero_extend.
    rewrite Hsz. by rewrite andTb.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- le Hlo <- <-.
    rewrite He1 /=. rewrite He2 /=.
    rewrite Hw /=. rewrite Hw' /= Hlo /=. by exists (Vword (y+h3)).
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- le Hlo <- <-. rewrite He1 /= He2 /= Hw Hw' /= Hlo /=.
  by exists (Vword (y + h3)). 
Qed.

Lemma saddPl s ty e1 e2 v l:
let e' := (sadd ty e1 e2).1 in
let t := (sadd ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Oadd ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
by case: ty; eauto using sadd_intPl, sadd_wPl.
Qed.

Lemma ssub_intPl s e1 e2 v l:
let e' := (ssub_int e1 e2).1 in
let t := (ssub_int e1 e2).2 in
sem_pexpr gd s (Papp2 (Osub Op_int) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /ssub_int. rewrite /trans_sem.
case: (is_constP e1) => [n1 | {e1} e1];
case: (is_constP e2) => [n2 | {e2} e2] // /=.
+ move=> H1. exists (n1 - n2)%Z. split. auto.
  by case: H1 => -> _.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hy <- le Hlo <- <-; subst.
  rewrite He /=. exists (n1 - y)%Z. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= [] hz z' [] _ [] <-.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int /= Hy <- le Hlo <- <-.
  case: eqP.
  - move=> Hn2. rewrite He Hn2 Hy /=; subst. exists y. split=> //. by rewrite Z.sub_0_r.
  move=> Hn2 /=. t_xrbindP. rewrite He /= Hy /=; subst. exists (y - n2)%Z. 
  rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= [] hz z' [] _ [] <-.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y /of_val_int Hy h1 /of_val_int Hy' <- le Hlo <- <-; subst.
  rewrite He He' /=. exists (y - h1)%Z. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= [] hz z' [] _ [] <-.
Qed.

Lemma ssub_wPl s sz e1 e2 v l:
let e' := (ssub_w sz e1 e2).1 in
let t := (ssub_w sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Osub (Op_w sz)) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /ssub_w. rewrite /trans_sem.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He' /=. move=> h4.
  rewrite /sem_sop2 /=. t_xrbindP. move=> y Hw h3 Hw' <- le Hlo <- Hl.
  have /= /(_ LO) := is_wconstP gd s h1; have /= /(_ LO) := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2. move=> Hw2. rewrite He /=.
  move=> h5 [] <-. rewrite Hw /=. move=> [] <- /=.
  rewrite He' in He2. case: He2 => He21 He22.
  rewrite He21 in Hw'. rewrite Hw2 in Hw'. case: Hw'=> [] ->.
  rewrite wrepr_unsigned /= -Hl /=. exists (Vword (y - h3)). 
  rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> sv /= hz z' hz' [] <-.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move => h y Hyv h3 Hyv' <- le Hlo <- <-. 
  rewrite He /= He' /= Hlo /= Hyv Hyv' /=.
  by exists (Vword (y - h3)).
+ case: eqP => // hz /=. 
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have /= /(_ LO) := is_wconstP gd s h2.
    rewrite He' /=. move=> -> /= h y Hw' h3 [] <- <- le Hlo <- <-. rewrite He /=.
    apply of_val_word in Hw'. move: Hw'. move=> [] sz' [] x0 [] Hsz -> ->.
    rewrite hz /=. rewrite GRing.subr0. rewrite /word_uincl /zero_extend.
    exists (Vword x0). rewrite Hsz. by rewrite andTb.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- le Hlo <- <-.
    rewrite He1 /= He2 /= Hw /= Hw' /= Hlo /=. by exists (Vword (y - h3)).
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- le Hlo <- <-. rewrite He1 /= He2 /= Hw Hw' Hlo /=. 
  by exists (Vword (y - h3)).
Qed.

Lemma ssubPl s ty e1 e2 v l:
let e' := (ssub ty e1 e2).1 in
let t := (ssub ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Osub ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
by case: ty; eauto using ssub_intPl, ssub_wPl.
Qed.

Lemma smul_intPl s e1 e2 v l:
let e' := (smul_int e1 e2).1 in
let t := (smul_int e1 e2).2 in
sem_pexpr gd s (Papp2 (Omul Op_int) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /smul_int. rewrite /trans_sem.
case: (is_constP e1) => [n1| {e1} e1];
case: (is_constP e2) => [n2| {e2} e2] /=.
+ move=> [] <- _. exists (n1 * n2)%Z.
  by split.
+ t_xrbindP. move=> [yv yl] He2. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hyv <- le Hlo <- <-.
  case:eqP => [-> //|_].
  - rewrite /=. exists 0%Z. by split.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He2. rewrite He2. exists y.
    split. auto. by rewrite Z.mul_1_l /=.
  t_xrbindP. rewrite He2 /=.
  rewrite /sem_sop2 /=. t_xrbindP. rewrite Hyv /=.
  exists (n1 * y)%Z. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> st /= _ z _ [] <-. 
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hyv <- le Hlo <- <-.
  case:eqP => [-> //|_].
  - rewrite /=. exists 0%Z. by rewrite Z.mul_0_r.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He1. rewrite He1.
    exists y. by rewrite Z.mul_1_r /=.
  t_xrbindP. rewrite He1 /=.
  rewrite /sem_sop2 /=. t_xrbindP. rewrite Hyv /=.
  exists (y * n2)%Z. rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> st /= _ z _ [] <-. 
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hyv h1 Hyv' <- le Hlo <- <-. rewrite He1 He2 /= Hyv Hyv' Hlo /=.
  by exists (y*h1)%Z.
Qed.

Lemma smul_wPl s sz e1 e2 v l:
let e' := (smul_w sz e1 e2).1 in
let t := (smul_w sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Omul (Op_w sz)) e1 e2)  = ok (v, l) ->
exists v',sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /smul_w. rewrite /trans_sem. 
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
(* Some n1, Some n2 *)
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  have /= /(_ LO) := is_wconstP gd s h1. have /= /(_ LO) := is_wconstP gd s h2.
  t_xrbindP. rewrite He1 He2 /=. 
  move=> [yv1 yl1] [] <- _ -> [yv2 yl2] [] <- hl ->.
  move=> h6 h7 [] <- h9 [] <- <- le Hlo <- <- /=. rewrite wrepr_unsigned.
  exists (Vword (n1 * n2)). rewrite /leak_sop2 in Hlo.
  move: Hlo. t_xrbindP. by move=> st /= hw wsz hw' [] <-.
+ case: eqP => hn1.
  (* Some n1 (n1=0), None *) 
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> [yv1 yl1] [] <- hl -> h3 h4 [] <- h6 Hyv' <- le Hlo <- <-.
    rewrite wrepr_unsigned hn1 /=. rewrite GRing.mul0r /=.
    rewrite /leak_sop2 in Hlo.
    move: Hlo. t_xrbindP. move=> st /= hw wsz hw' [] <-. by eexists (Vword 0).
  - case: eqP => hn2.
    (* Some n1 (n1=1), None *)
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- le Hlo <- <-.
      rewrite He'. have /= /(_ LO) := is_wconstP gd s h1. 
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He in He1'.
      case: He1' => <- _. rewrite Hyv /=.
      move=> [] ->. rewrite hn2. rewrite GRing.mul1r.
      case: (of_val_word Hyv') => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      exists (Vword w). split. auto.
      rewrite /word_uincl /zero_extend. by rewrite Hsz /=.
    (* Some n1 (n1!=0,1), None *)
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2 /=. rewrite /sem_sop2 /= /leak_sop2.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- lo yt happ yt' happ' /= [] <- <- <- /=. rewrite He2 /=.
    rewrite wrepr_unsigned truncate_word_u. rewrite Hyv' /=.
    have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
    move=> [yv1 yl1] He1'. rewrite He1 in He1'. case: He1' => <- _. rewrite Hyv /=.
    move=> [] -> /=. exists (Vword (n1 * h3)). by split.
+ case: eqP => hn1.
(* None, Some n2 (n2 = 0) *)
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> [yv1 yl1] [] <- _ -> h3 h4 Hyv h6 [] <- <- le Hlo <- <-.
    rewrite wrepr_unsigned hn1 /=. rewrite GRing.mulr0.
    eexists. split. auto. rewrite /leak_sop2 in Hlo. move: Hlo. 
    by t_xrbindP=> st /= hw wsz hw' [] <- /=. by rewrite /=.
  - case: eqP => hn2.
    (* None, Some n2 (n2 != 0, n2 = 1 *)
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- le Hlo <- <-.
      rewrite He /=. have /= /(_ LO) := is_wconstP gd s h2.
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He' in He1'. case: He1' => <- _.
      rewrite Hyv' /=. move=> [] ->. rewrite hn2. rewrite GRing.mulr1.
      case: (of_val_word Hyv) => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      exists (Vword w). split. auto. rewrite /word_uincl /zero_extend.
      by rewrite Hsz /=.
    (* None, Some n2 (n2 != 0, 1 *)
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2 /=. rewrite /sem_sop2 /= /leak_sop2.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- lo yt happ yt' happ' /= [] <- <- <- /=. rewrite He1 /=.
    rewrite wrepr_unsigned truncate_word_u. rewrite Hyv /=.
    have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP.
    move=> [yv1 yl1] He2'. rewrite He2 in He2'. case: He2' => <- _. rewrite Hyv' /=.
    move=> [] -> /=. exists (Vword (y * n2)). by split.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y Hyv h3 Hyv' <- le Hlo <- <-.
  rewrite He He' /=. rewrite Hyv Hyv' Hlo /=.
  by exists (Vword (y * h3)). 
Qed.

Lemma smulPl s ty e1 e2 v l:
let e' := (smul ty e1 e2).1 in
let t := (smul ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Omul ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
by case: ty; eauto using smul_intPl, smul_wPl.
Qed.

Lemma s_eqPl s ty e1 e2 v l:
let e' := (s_eq ty e1 e2).1 in
let t := (s_eq ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Oeq ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. 
rewrite /s_eq; case:ifP => [ /eq_exprP Hs | _]; rewrite /=.
+ move: (Hs gd s). move=> Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'. rewrite Hs' in He.
  rewrite He' in He. case: He=> -> ->.
  rewrite /sem_sop2 ; case: ty => [ | sz ] /=.
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- le Hlo <- _.
    exists true. by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _.
  exists true. by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _. exists (n1 =? n2)%Z. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- le Hlo <- <-. rewrite He /=.
     rewrite Hyv /= Hlo /=. by exists (n1 =? y)%Z.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- le Hlo <- <-. rewrite He1 /= Hyv /= Hlo /=.
     by exists (y =? n2)%Z.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- le Hlo <- <-. 
     rewrite He He' /= Hyv Hyv' Hlo /=. by exists (y =? h1)%Z.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> y0 [] <- /=. move => -> /= h3 h4 [] <-.
    have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> y [] <- /= -> /= h5 [] <- <- le Hlo <- _.
    by exists (n1 == n2)%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- le Hlo <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' Hlo /=.
    by exists (y == h3)%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- le Hlo <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' Hlo /=.
    by exists (y==h2)%Z.
Qed.

Lemma sneqPl s ty e1 e2 v l:
let e' := (sneq ty e1 e2).1 in
let t := (sneq ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Oneq ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. 
rewrite /sneq /s_eq; case:ifP => [ /eq_exprP Hs | _]; rewrite /=.
+ move: (Hs gd s). move=> Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'. rewrite Hs' in He.
  rewrite He in He'. case: He' => <- <- /=.
  rewrite /sem_sop2 ; case: ty => [ | sz ] /=.
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- le Hlo <- _.
    exists false. by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _.
  exists false. by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _. exists (~~ (n1 =? n2))%Z. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- le Hlo <- <-. rewrite He /=.
     rewrite Hyv /= Hlo. by exists (~~(n1 =? y))%Z.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- le Hlo <- <-. rewrite He1 /=.
     rewrite Hyv /= Hlo. by exists (~~(y =? n2))%Z.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- le Hlo <- <-. rewrite He He' /=.
     rewrite Hyv Hyv' /= Hlo. by exists (~~(y =? h1))%Z.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> y0 [] <- /=.
    move => -> /= h3 h4 [] <-.
    have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> y [] <- /= -> /= h5 [] <- <- le Hlo <- _.
    by exists (~~(n1 == n2))%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- le Hlo <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /= Hlo.
    by exists (~~(y == h3))%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- le Hlo <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' Hlo /=.
    by exists (~~(y==h2))%Z.
Qed.

Lemma is_cmp_constP s ty e z :
  is_cmp_const ty e = Some z →
  match ty with
  | Cmp_int => e = Pconst z
  | Cmp_w sg sz =>
    exists x, exists l,
    sem_pexpr gd s e = ok (x, l) /\
    exists2 w,
    to_word sz x = ok w &
    match sg with
    | Signed => wsigned w = z
    | Unsigned => wunsigned w = z
    end
  end.
Proof.
  case: ty => /=.
  - by case: is_constP => // ? /(@Some_inj _ _ _) <-.
  move => sg sz /oseq.obindI [] w [] /(is_wconstP gd s).
  t_xrbindP. move=> [yv yl] He Hw [<-{z}]. rewrite He /=.
  exists yv. exists yl. split. auto.
  exists w => //. by case: sg.
Qed.

Ltac is_cmp_const s :=
  match goal with
  | |- context[ is_cmp_const ?ty ?e ] =>
    case: is_cmp_const (@is_cmp_constP s ty e);
    [ let n := fresh in move => n /(_ _ erefl); move: n | ]
  end.

Lemma sltPl s ty e1 e2 v l:
let e' := (slt ty e1 e2).1 in
let t := (slt ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Olt ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. rewrite /slt;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] -> <- le Hlo <- _.
    exists false. by rewrite Z.ltb_irrefl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _. 
    exists false. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 <? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- le Hlo <- _. exists (wsigned w1 <? wsigned w2)%Z.
      by rewrite ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- le Hlo <- _. exists (wunsigned w1 <? wunsigned w2)%Z.
    by rewrite ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
Qed.

Lemma slePl s ty e1 e2 v l:
let e' := (sle ty e1 e2).1 in
let t := (sle ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Ole ty) e1 e2) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. rewrite /sle;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- le Hlo <- _.
    exists true. by rewrite Z.leb_refl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _. 
    exists true. by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 <=? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- le Hlo <- _. exists (wsigned w1 <=? wsigned w2)%Z.
      by rewrite ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- le Hlo <- _. exists (wunsigned w1 <=? wunsigned w2)%Z.
    by rewrite ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
Qed.

Lemma sgtPl s ty e1 e2 v l:
let e' := (sgt ty e1 e2).1 in
let t := (sgt ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Ogt ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. rewrite /sgt;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- le Hlo <- _.
    exists false. by rewrite Z.gtb_ltb Z.ltb_irrefl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _. 
    exists false. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 >? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- le Hlo <- _. exists (wsigned w1 >? wsigned w2)%Z.
      by rewrite Z.gtb_ltb ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- le Hlo <- _. exists (wunsigned w1 >? wunsigned w2)%Z.
    by rewrite Z.gtb_ltb ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
Qed.

Lemma sgePl s ty e1 e2 v l:
let e' := (sge ty e1 e2).1 in
let t := (sge ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Oge ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem. rewrite /sge;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- le Hlo <- _.
    exists true. by rewrite Z.geb_leb Z.leb_refl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- le Hlo <- _. 
    exists true. by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. by exists (n1 >=? n2)%Z.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- le Hlo <- _. exists (wsigned w1 >=? wsigned w2)%Z.
      by rewrite Z.geb_leb ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- le Hlo <- _. exists (wunsigned w1 >=? wunsigned w2)%Z.
    by rewrite Z.geb_leb ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> le Hlo <- <-. rewrite Hs Hlo /=. by exists h3.
Qed.

Lemma sbitwPl i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 v' s l:
let e' := (sbitw i z sz e1 e2).1 in
let t := (sbitw i z sz e1 e2).2 in
(∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
  sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v ->
      v = Vword (z sz (zero_extend sz w1) (zero_extend sz w2))) ->
sem_pexpr gd s (Papp2 (i sz) e1 e2) = ok (v', l) ->
exists v'', sem_pexpr gd s e' = ok (v'', (trans_sem t (v', l)).2) /\
value_uincl (trans_sem t (v', l)).1 v''.
Proof.
rewrite /trans_sem.
rewrite /sbitw => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He2 in He2'. case: He2'=> -> -> /=.
  move=> Hyv Hyv' h5 Hs' le Hlo <- <-.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  exists (Vword (wrepr sz (wunsigned (z sz (zero_extend sz w1) (zero_extend sz w2))))).
  split. auto. rewrite He1 in He1'. case: He1'=> He11 He12.
  rewrite He11 in Hs'. rewrite Hw1 in Hs'. rewrite Hw2 in Hs'.
  move: (h sz1 w1 sz2 w2 h5 Hs'); subst. move=> hh /=; subst. by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'. case: He1'=> <- <- /=.
  move=> Hyv h4 Hs' le Hlo <- <-.
  rewrite He1 He2 /=. rewrite Hs' /= Hlo /=. by exists h4. 
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs le Hlo <- <-.
rewrite Hs Hlo /=. by exists h4.
Qed.

Lemma slandPl s ty e1 e2 v l:
let e' := (sland ty e1 e2).1 in
let t := (sland ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Oland ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma slorPl s ty e1 e2 v l:
let e' := (slor ty e1 e2).1 in
let t := (slor ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Olor ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma slxorPl s ty e1 e2 v l:
let e' := (slxor ty e1 e2).1 in
let t := (slxor ty e1 e2).2 in
sem_pexpr gd s (Papp2 (Olxor ty) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma sbitw8Pl i (z: ∀ sz, word sz → word U8 → word sz) sz e1 e2 v' s l:
let e' := (sbitw8 i z sz e1 e2).1 in
let t := (sbitw8 i z sz e1 e2).2 in
(∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
  sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v ->
      v = Vword (z sz (zero_extend sz w1) (zero_extend U8 w2))) ->
sem_pexpr gd s (Papp2 (i sz) e1 e2) = ok (v', l) ->
exists v'', sem_pexpr gd s e' = ok (v'', (trans_sem t (v', l)).2 ) /\
value_uincl (trans_sem t (v', l)).1 v''.
Proof.
rewrite /trans_sem.
rewrite /sbitw8 => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'.
  case: He1' => -> _.
  case: He2' => -> _. move=> Hyv Hyv' h5 Hs' le Hlo <- <-.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  rewrite Hw1 Hw2 in Hs'. move: (h sz1 w1 sz2 w2 h5 Hs'). 
  move=> -> /=. exists (Vword (wrepr sz (wunsigned (z sz (zero_extend sz w1) (zero_extend U8 w2))))).
  by rewrite wrepr_unsigned /=; subst.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' le Hlo <- <-.
  rewrite He1 He2 /= Hs' Hlo /=. by exists h4. 
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs le Hlo <- <-.
rewrite Hs Hlo /=. by exists h4.
Qed.

Lemma slslPl s sz e1 e2 v l:
let e' := (sshl sz e1 e2).1 in
let t := (sshl sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Olsl sz) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma slsrPl s sz e1 e2 v l:
let e' := (sshr sz e1 e2).1 in
let t := (sshr sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Olsr sz) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2 ) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma sasrPl s sz e1 e2 v l:
let e' := (ssar sz e1 e2).1 in
let t := (ssar sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Oasr sz) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma sdivPl s sz e1 e2 v l:
let e' := (sdiv sz e1 e2).1 in
let t := (sdiv sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Odiv sz) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem.
case: sz => [ | u sz] /=.
+ rewrite /soint.
  case: (is_constP e1) => [n1| {e1} e1].
  case: (is_constP e2) => [n2| {e2} e2] /=; eauto.
  - move=> [] <- Hl. by exists (n1 / n2)%Z.
  - t_xrbindP. rewrite /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> h1 -> <- le Hlo <- <- /=.
    rewrite Hlo /=. by exists (y / h1)%Z.
rewrite /sbituw.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
- case:eqP => // neq.
  t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
  t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
  move=> h5 -> <- le Hlo <- <-. t_xrbindP. rewrite Hlo /=. by exists (Vword h5).
  t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'. case: He1' => -> _.
  case: He2' => -> _. move=> Hyv Hyv' h4 Hs' le /= Hlo <- <- /=. 
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
  rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
  rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
  move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
  case: ifP => //. move=> H.  move=> h5 [] <- <-.
  exists (Vword (wrepr sz (wunsigned (signed (@wdiv) (@wdivi) u sz n1 n2)))).
  rewrite -Hn /=. rewrite /zero_extend wrepr_unsigned. case: u Hlo=> //=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' le Hlo <- <-.
  rewrite He1 He2 /=. rewrite Hs' Hlo /=. by exists h4.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs le Hlo <- <-.
rewrite Hs Hlo /=. by exists h4.
Qed.

Lemma smodPl s sz e1 e2 v l:
let e' := (smod sz e1 e2).1 in
let t := (smod sz e1 e2).2 in
sem_pexpr gd s (Papp2 (Omod sz) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /trans_sem.
case: sz => [ | u sz] /=.
+ rewrite /soint.
  case: (is_constP e1) => [n1| {e1} e1].
  case: (is_constP e2) => [n2| {e2} e2] /=; eauto.
  - move=> [] <- Hl. by exists (n1 mod n2)%Z.
  - t_xrbindP. rewrite /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> h1 -> <- le Hlo <- <- /=.
    rewrite Hlo /=. by exists (y mod h1)%Z.
rewrite /sbituw.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
- case:eqP => // neq.
  t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
  t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
  move=> h5 -> <- le Hlo <- <-. t_xrbindP. rewrite Hlo /=. by exists (Vword h5).
  t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have /= /(_ LO) := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'.
  case: He1' => -> _. case: He2' => -> _. move=> Hyv Hyv' h4 Hs' le Hlo <- <- /=. 
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
  rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
  rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
  move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
  case: ifP => //. move=> H.  move=> h5 [] <- <-.
  exists (Vword (wrepr sz (wunsigned (signed (@wmod) (@wmodi) u sz n1 n2)))).
  rewrite -Hn /=. rewrite /zero_extend wrepr_unsigned. case: u Hlo=> //=. 
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have /= /(_ LO) := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' le Hlo <- <-.
  rewrite He1 He2 /=. rewrite Hs' Hlo /=. by exists h4.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs le Hlo <- <-.
rewrite Hs Hlo /=. by exists h4.
Qed.

Lemma svaddPl s ve ws e1 e2 v l:
let e' := (svadd ve ws e1 e2).1 in
let t := (svadd ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovadd ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma svsubPl s ve ws e1 e2 v l:
let e' := (svsub ve ws e1 e2).1 in
let t := (svsub ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovsub ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma svmulPl s ve ws e1 e2 v l:
let e' := (svmul ve ws e1 e2).1 in
let t := (svmul ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovmul ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: sbitwPl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma svshlPl s ve ws e1 e2 v l:
let e' := (svshl ve ws e1 e2).1 in
let t := (svshl ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovlsl ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: @sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma svshrPl s ve ws e1 e2 v l:
let e' := (svshr ve ws e1 e2).1 in
let t := (svshr ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovlsr ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: @sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma svsarPl s ve ws e1 e2 v l:
let e' := (svsar ve ws e1 e2).1 in
let t := (svsar ve ws e1 e2).2 in
sem_pexpr gd s (Papp2 (Ovasr ve ws) e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
apply: @sbitw8Pl => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
Qed.

Lemma s_op2Pl s o e1 e2 v l:
let e' := (s_op2 o e1 e2).1 in
let t := (s_op2 o e1 e2).2 in
sem_pexpr gd s (Papp2 o e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
  case: o;eauto using sandPl, sorPl, saddPl, smulPl, ssubPl, sdivPl, smodPl,
                      s_eqPl, sneqPl, sltPl, slePl, sgtPl, sgePl,
                      slandPl, slorPl, slxorPl, slslPl, slsrPl, sasrPl,
                      svaddPl, svsubPl, svmulPl, svshlPl, svshrPl, svsarPl.
Qed.

Lemma s_opNPl s op es v l:
let e' := (s_opN op es).1 in
let t := (s_opN op es).2 in
sem_pexpr gd s (PappN op es)  = ok (v, l) ->
sem_pexpr gd s e' = ok (trans_sem t (v, l)).
Proof.
  rewrite /trans_sem. rewrite /s_opN.
  case hi: (mapM _ _) => [ i | ] /=; last by rewrite /= => ->.
  case heq: (sem_opN op i) => [ v'' | ] /=; last by rewrite /= => ->.
  case: v'' heq => //= sz w'; try by rewrite /= => -> [] <-.
  case: op => sz' pe /=.
  rewrite /sem_opN /=; apply: rbindP => w h /ok_word_inj [] ?; subst => /= <-{w'}.
  rewrite /sem_sop1 /= wrepr_unsigned -/(sem_pexprs _ _). t_xrbindP.
  move=> vls hes.
  have : unzip1 vls = i. 
  + elim: es i vls hi hes {h} => /=.
    + by move=> ?? [<-] [<-].
    move=> e es hrec i vls; t_xrbindP => v1 h1 vs /hrec hr <- ? h2 ? /hr <- <- /=.
    by case: e h1 h2 => //= ? [->] [<-].
  by move=> -> /=; rewrite h /= => v'' sz'' [] <- /= <- le Hlo -> <-. 
Qed.


Definition vconst c :=
  match c with
  | Cbool b => Vbool b
  | Cint z => Vint z
  | Cword sz z => Vword z
  end.

Definition valid_cpm (vm: vmap)  (m:cpm) :=
  forall x n, Mvar.get m x = Some n -> get_var vm x = ok (vconst n).

Lemma lt_composeE p x y :
  leak_E p (lt_compose x y) =1 leak_E p (LT_compose x y).
Proof.
  rewrite /lt_compose.
  case: x; first by [].
  all: by case: y.
Qed.
Global Opaque lt_compose.

Section CONST_PROP_EP.
  Context s m (Hvalid: valid_cpm (evm s) m).

  Let P e : Prop := forall v l, let e' := (const_prop_e m e).1 in
                    let t := (const_prop_e m e).2 in
                    sem_pexpr gd s e = ok (v, l) ->
                    exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
                    value_uincl (trans_sem t (v, l)).1 v'.

  Let Q es : Prop := forall vs, let et := map (const_prop_e m) es in
                    let e' := unzip1 et in
                    let t := unzip2 et in
                    sem_pexprs gd s es = ok vs ->
                    exists vs', sem_pexprs gd s e' = ok vs' /\
                    (* FIXME : map2 ... -> leak_F (LT_seq t) l = l' *)
                    List.Forall2 value_uincl (unzip1 vs) (unzip1 vs') /\
                    LSub (unzip2 vs') = leak_E stk (LT_map t) (LSub (unzip2 vs)).
                    (* comment: here leak_F produces leak_e and unzip2 vs' is seq of leak_e *)
                    (* better solution *)
                    (* exists2 v', sem_pexprs_e gd s e' = ok (v', leak_F (LT_seq t) l) & List.Forall2 value_uincl v v'. *)


Lemma const_prop_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
Proof.
apply: pexprs_ind_pair; subst P Q; split => /=;
try (intros; clarify; eauto; fail).
- move=> vs [] <-. exists [::]. split. auto. split. by rewrite /=; auto. auto.
- move=> e H es Hs. t_xrbindP. move=> hh [yv1 yl1] He h1 Hes <-.
  move: (H yv1 yl1 He). move=> [] x [] -> Hv /=.
  move: (Hs h1 Hes). move=> [] x0 [] -> [] Hv' /= Hl' /=.
  exists (((x, leak_E stk (const_prop_e m e).2 yl1) :: x0)).
  split. auto. split. apply List.Forall2_cons. auto. auto.
  case: Hl' => <-. auto.
- move=> z v l [] <- <-. by exists z.
- move=> b v l [] <- <-. by exists b.
- move=> n v l [] <- <-. by exists (Varr (WArray.empty n)).
- move=> x v l. move: Hvalid => /(_ x).
  case: Mvar.get => [n /(_ _ erefl) | _ /= -> ]; last by eauto.
  move=> -> /= [] <- Hl.
  case: n => [ b | n | sz w ] /=.
  + by exists b. + by exists n.
  exists (Vword (wrepr sz (wunsigned w))). split.
  auto. by rewrite wrepr_unsigned.
- move=> sz x e He. move=> v l.
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
  t_xrbindP. move=> [yv yl] He' /=. move: (He yv yl He').
  move=> [] xv [] He'' /= Hv. move=> h0 Hyv h2 Hw <- <-.
  rewrite Hg /=. rewrite He'' /=.
  move: (value_uincl_int Hv Hyv). move=> [] Hyv' ->.
  rewrite Hyv' in Hyv. rewrite Hyv /=. rewrite Hw /=.
  by exists (Vword h2).
- move=> sz x e He. move=> v l.
  t_xrbindP. move=> y h Hg Hp [yv yl] He' h4 Hp' h6 Hr <- <-.
  move: (He yv yl He'). move=> [] xv [] He'' /= Hv.
  exists (Vword h6). rewrite Hg /=. rewrite Hp /=. rewrite He'' /=.
  move: (value_uincl_word Hv Hp'). move=> -> /=.
  rewrite Hr /=. by split. 
+ move=> op e He. move=> v l. t_xrbindP.
  move=> [yv yl] /He [] x [] He' Hyv h0 Hop le Hlo <- <- /=.
  rewrite lt_composeE.
  apply /s_op1Pl. rewrite /=. rewrite He' /=.
  move: (vuincl_sem_sop1 Hyv Hop). move=> -> /=.
  by have -> /= := leak_sop1_eq Hyv Hlo.
+ move=> op e1 He1 e2 He2 v l. t_xrbindP.
  move=> [yv yl] /He1 [] x [] He1' Hyv.
  move=> [yv1 yl'] /He2 [] x1 [] He2' Hyv'.
  move=> h2 Ho le Hlo <- <-.
  rewrite lt_composeE.
  apply /s_op2Pl. rewrite /=. rewrite He1' /=.
  rewrite He2' /=. move: (vuincl_sem_sop2 Hyv Hyv' Ho).
  move=> -> /=. by have -> /= := leak_sop2_eq Hyv Hyv' Hlo.
+ t_xrbindP => op es ih ve lv vs ok_vs v ok_v le Hlo <- <-.
  move: ih => /(_ _ ok_vs) [] vs' [] ok_vs' [] hvs' hk.
  have [v' ok_v' hv' ] := vuincl_sem_opN ok_v hvs'.
  exists v'; split; last exact: hv'.
  set esk := map (const_prop_e m) es.
  have /= := @s_opNPl s op (unzip1 esk) v' (LSub [:: LSub (unzip2 vs'); le]).
  have Hlo' := leak_opN_eq hvs' Hlo.
  by rewrite lt_composeE -/(sem_pexprs gd s (unzip1 esk)) ok_vs' /= ok_v' hk /= Hlo' /= => /(_ erefl) ->.
move=> t e He e1 He1 e2 He2 v l. t_xrbindP.
move=> [yv yl] /He/= [] x [] He' Hyv h0 
/(value_uincl_bool Hyv) [] Hx Hxl; subst.
move=> [yv1 yl1] /He1/= [] x1 [] He1' Hyv1.
move=> [yv2 yl2] /He2/= [] x3 [] He2' Hyv2.
move=> h6 /(truncate_value_uincl Hyv1) [] x Ht Hv h8
  /(truncate_value_uincl Hyv2) [] x0 Ht' Hv'.
move=> <- <- /=.
rewrite /s_if. case: is_boolP He'.
- move=> a. case: (a).
  * move=> /= Htr. case: Htr => <- Hlt. exists x1.
    rewrite He1' /=. split. auto. move : (value_uincl_truncate_val Ht).
    move=> Ht1. move : (value_uincl_trans Hv Ht1).
    by move=> /= Htr. 
  move=> /= [] <- Hl /=. rewrite He2' /=. exists x3.
  move : (value_uincl_truncate_val Ht')=> Ht1.
  move : (value_uincl_trans Hv' Ht1)=> Ht2. by split=> //=.
move=> e' /= -> /=. rewrite He1' /= He2' /= Ht /= Ht' /=.
exists (if h0 then x else x0). split=> //=.
by case: (h0).
Qed.

End CONST_PROP_EP.

Definition const_prop_eP e s m h :=
  (@const_prop_e_esP s m h).1 e.

Definition const_prop_esP es s m h :=
  (@const_prop_e_esP s m h).2 es.

Lemma remove_cpm1P x v m s1 s1' :
  write_var x v s1 = ok s1' ->
  valid_cpm (evm s1) m ->
  valid_cpm (evm s1') (Mvar.remove m x).
Proof.
  move=> Hw Hv z n;rewrite Mvar.removeP;case: ifPn => //= ? /Hv.
  move: Hw;apply: rbindP => vm;apply: on_vuP => [ w ? <- [<-] | ].
  + by rewrite /get_var /= Fv.setP_neq.
  by case: ifP => //= _ ? [<-] [<-] /=;rewrite /get_var /= Fv.setP_neq.
Qed.

Lemma add_cpmP s1 s1' m x e tag ty v1 v v' :
  sem_pexpr gd s1 e = ok v1 ->
  value_uincl v v1.1 ->
  truncate_val ty v = ok v' ->
  write_lval gd x v' s1 = ok s1' ->
  valid_cpm (evm s1'.1) m ->
  valid_cpm (evm s1'.1) (add_cpm m x tag ty e).
Proof.
  rewrite /add_cpm;case: x => [xi | x | x | x] //= He.
  case: tag => //.
  case: e He => // [n | b | [] // sz [] //= q ] [<-].
  + case: v => //= ?;last first.
    + by rewrite compat_typeC => /eqP ->; case: ty.
    move=> -> /truncate_val_int [_ ->].
    case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
    have := Hv z n0.
    case: ({| vtype := sint; vname := xn |} =P z).
    + move=> <- /=;rewrite Mvar.setP_eq=> ? -[] <-;by rewrite /get_var Fv.setP_eq.
    by move=> /eqP Hneq;rewrite Mvar.setP_neq.
  + case: v => //= ?;last first.
    + by rewrite compat_typeC => /eqP ->; case: ty.
    move=> -> /truncate_val_bool [_ ->].
    case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
    have := Hv z n0.
    case: ({| vtype := sbool; vname := xn |} =P z).
    + move=> <- /=;rewrite Mvar.setP_eq=> ? -[] <-;by rewrite /get_var Fv.setP_eq.
    by move=> /eqP Hneq;rewrite Mvar.setP_neq.
  case: v => //= s ;last first.
  + by rewrite compat_typeC; case: s => //= s' _;case: ty.
  move=> w /andP[] Ule /eqP -> /truncate_val_word [] szw [] -> hle -> /=.
  rewrite !(zero_extend_wrepr _ Ule, zero_extend_wrepr _ (cmp_le_trans hle Ule), zero_extend_wrepr _ hle).
  case: x => -[] [] //= szx xn vi [] <- /= Hv z /= n.
  have := Hv z n.
  case: ({| vtype := sword szx; vname := xn |} =P z).
  + move=> <- /=. rewrite Mvar.setP_eq=> ? -[] <-; rewrite /get_var Fv.setP_eq /=.
    by f_equal; case: Sumbool.sumbool_of_bool => h;rewrite h.
  by move=> /eqP Hneq;rewrite Mvar.setP_neq.
Qed.

Lemma merge_cpmP rho m1 m2 :
  valid_cpm rho m1 \/ valid_cpm rho m2 ->
  valid_cpm rho (merge_cpm m1 m2).
Proof.
  move=> Hv x n;rewrite /merge_cpm Mvar.map2P //.
  case Heq1 : (Mvar.get m1 x) => [n1|//]; case Heq2 : (Mvar.get m2 x) => [n2|//].
  case: eqP=> //.
  by move=> ? [] ?;do 2 subst;elim: Hv => Hv;apply Hv.
Qed.

Lemma const_prop_rvP s1 s2 m x v:
  let c' := ((const_prop_rv m x).1).1 in
  let e' := ((const_prop_rv m x).1).2 in
  let t' := ((const_prop_rv m x).2) in 
  valid_cpm (evm s1) m ->
  write_lval gd x v s1 = Ok error s2 ->
  valid_cpm (evm s2.1) c' /\
  write_lval gd e' v s1 = ok ((trans_sem_estate t' s2).1, (trans_sem_estate t' s2).2).
Proof.
  rewrite /trans_sem_estate.
  case:x => [ii t | x | sz x p | sz x p] /= Hv.
  + t_xrbindP. move=> y H <-.
    move: (write_noneP)=> Hw.
    move: (Hw s1 y t v H). move=> [] Hs _. rewrite -Hs in Hv.
    split. auto. by rewrite H /=.
  + t_xrbindP. move=> y H <-.
    split. apply: remove_cpm1P H Hv.
    by rewrite H /=.
  + t_xrbindP. move=> y h -> /= -> /=.
    move=> [yv yl] He h4 /value_uincl_word Hyv h6 hv.
    move=> h8 Hm <- /=.
    move: (const_prop_eP). move=> Hc. move: (Hc p s1 m Hv yv yl He).
    move=> [] x0 [] -> Hv' /=.
    rewrite /= in Hv'. move: (Hyv x0 Hv').
    move=> -> /=. rewrite hv /=. rewrite Hm /=.
    split. auto. auto.
  apply: on_arr_varP;rewrite /on_arr_var => n t Htx -> /=.
  t_xrbindP. move=> [yv yl] He h0 /value_uincl_int Hy h2 Hw' /= h4 Hw h6 Hs <- /=.
  move: (const_prop_eP). move=> H. move: (H p s1 m Hv yv yl He).
  move=> [] x0 [] -> /= hv.
  have Hww : write_var x (Varr h4) s1 = ok (Estate (emem s1) h6).
  by rewrite /write_var Hs. move: remove_cpm1P. move=> Hr.
  move: (Hr x (Varr h4) m s1 {| emem := emem s1; evm := h6 |} Hww Hv).
  move=> /= Hc. move: (Hy x0 hv). move=> [] /= H1 H2. rewrite H2 /=.
  rewrite Hw' /=. rewrite Hw /=. rewrite Hs /=.
  split. by auto. auto.
Qed.

Lemma const_prop_rvsP s1 s2 m xs vs lw:
  let c' := ((const_prop_rvs m xs).1).1 in
  let e' := ((const_prop_rvs m xs).1).2 in
  let t' := ((const_prop_rvs m xs).2) in 
  valid_cpm (evm s1) m ->
  (* write_lvals produces seq leak_e, lw is seq of leak_e *)
  write_lvals gd s1 xs vs = ok (s2, lw) ->
  valid_cpm (evm s2) c' /\
  write_lvals gd s1 e' vs = ok (s2, map2 (leak_E stk) t' lw).
                              (* [:: leak_F (LT_seq t') (LSub s2.2)]).*)
Proof.
  elim: xs vs m s1 s2 lw => [ | x xs Hrec] [ | v vs] //= m s1 s2 lw Hm /=.
  + move=> [] <- Hl. auto.
  t_xrbindP. move=> [s l] Hw [s' l'] /= Hws <- <- /=.
    move: const_prop_rvP. move=> Hcw. move: (Hcw s1 (s, l) m x v).
    case hcrv: const_prop_rv=>[m1 l1];case: m1 hcrv=> m1 c1 hcrv /=.
    move=> {Hcw} Hcw. move: (Hcw Hm Hw). move=> [] Hm1 Hw' {Hcw}.
    case hcrvs: const_prop_rvs=>[ms ls];case: ms hcrvs=> ms cs hcrvs /=.
    move:(Hrec vs m1 s s' l'). rewrite hcrvs /=. move=> {Hrec} Hrec.
    move: (Hrec Hm1 Hws). move=> [] Hm2 Hws'. split=> //.
    rewrite Hw' /=. by rewrite Hws' /=.
Qed.

Lemma remove_cpm_spec (m : cpm) (xs : Sv.t) (x : CmpVar.t):

  match Mvar.get (remove_cpm m xs) x with
  | Some n => Mvar.get m x = Some n /\ ~ Sv.In x xs
  | None   => Mvar.get m x = None \/ Sv.In x xs
  end.
Proof.
  rewrite /remove_cpm;apply SvP.MP.fold_rec_bis.
  + move=> s s' a Heq.
    by case: Mvar.get=> [? [] ??| [? | ?]]; [split=> //;SvD.fsetdec | left | right;SvD.fsetdec].
  + by case: Mvar.get=> [? | ]; [ split => //;SvD.fsetdec | left].
  move=> ?????;rewrite Mvar.removeP;case:ifPn => /eqP Heq.
  + by rewrite Heq=> _;right;SvD.fsetdec.
  by case: Mvar.get=> [? [] ??| [?|?]];[split=> //;SvD.fsetdec | left | SvD.fsetdec].
Qed.

Lemma remove_cpm2 m xs : Mvar_eq (remove_cpm (remove_cpm m xs) xs) (remove_cpm m xs).
Proof.
  move=> z;have := remove_cpm_spec (remove_cpm m xs) xs z.
  case: Mvar.get=> [? [] | [ | ]] // Hin.
  have := remove_cpm_spec m xs z.
  by case: Mvar.get=> // ? [] _ H;elim H.
Qed.

Lemma get_remove_cpm m xs x n:
  Mvar.get (remove_cpm m xs) x = Some n ->
  Mvar.get m x = Some n /\ ~Sv.In x xs.
Proof. by move=> H;have := remove_cpm_spec m xs x;rewrite H. Qed.

Lemma valid_cpm_rm rho1 rho2 xs m:
  rho1 = rho2 [\ xs] ->
  valid_cpm rho1 m ->
  valid_cpm rho2 (remove_cpm m xs).
Proof.
  move=> Hrho Hval x nx /get_remove_cpm [] Hm Hin.
  rewrite /get_var -Hrho //;apply (Hval _ _ Hm).  
Qed.

Lemma vrvP_e (x:lval) v s1 s2 lw:
  write_lval gd x v s1 = ok (s2, lw) ->
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ ty | | sz y e|sz y e ] //.
  + by t_xrbindP => ? /write_noneP [->] ? ->.
  + by t_xrbindP => ? ? /vrvP_var -> ->.
  + by t_xrbindP => z z0 He Hve v0 Hv0 t' Ht' w Hw m Hm <-.
  apply: on_arr_varP => n t; case: y => -[] ty yn yi /subtypeEl [n' /= [-> hle]] hget.
  t_xrbindP => we ve He Hve v0 Hv0 t' Ht' vm'.
  rewrite /set_var /= => -[<-] <- _ /=.
  move=> z Hz; rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec.
Qed.

Lemma remove_cpmP s s' m x v lw:
  write_lval gd x v s = ok (s', lw) ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv.
       apply: (valid_cpm_rm _ Hv).
       apply vrvP_e with v lw. auto.
Qed.

End GLOB_DEFS.

Section Section.

Context {LO: LeakOp}.

Instance const_prop_e_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq) const_prop_e.
Proof.
  move=> m1 m2 Hm e e' <- {e'}.
  elim: e => //=.
  + by move=> x; rewrite Hm.
  + by move=> ??? ->.
  + by move=> ??? ->.
  + by move=> ?? ->.
  + by move=> ?? -> ? ->.
  + move => op es h /=.
    (do 4 f_equal; last f_equal). + apply: map_ext=> e /InP He; exact: h. (*apply: map_ext => e /InP; exact: h.*)
    + do 2 f_equal. apply: map_ext=> e /InP He; exact: h.
    apply: map_ext=> e /InP He; exact: h.
  + move=> t e He e1 He1 e2 He2.
    by rewrite He He1 He2.
Qed.

Instance const_prop_rv_m :
  Proper (@Mvar_eq const_v ==> eq ==> RelationPairs.RelProd
                   (RelationPairs.RelProd (@Mvar_eq const_v) eq) eq) const_prop_rv.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => [ v | v | sz v p | sz v p] //=;rewrite Hm.
Qed.

Instance const_prop_rvs_m :
  Proper (@Mvar_eq const_v ==> eq ==> RelationPairs.RelProd
          (RelationPairs.RelProd (@Mvar_eq const_v) eq) eq) const_prop_rvs.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  elim: rv m1 m2 Hm => //= rv rvs Hrec m1 m2 Hm.
  have [/=]:= const_prop_rv_m Hm (refl_equal rv).
  case: const_prop_rv; move=>[m1' c1'] l1'; case: const_prop_rv; move=> [m2' c2'] l2'.
  rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
  move=> [] Hm' /= Hc Hl. move: (Hrec m1' m2' Hm').
  rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
  case: const_prop_rvs; move=>[m1'' c1''] l1''; case: const_prop_rvs; move=> [m2'' c2''] l2'' [].
  rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
  move=> [] Hm'' /= Hc' Hl'. split. rewrite /=. split. by rewrite /=.
  by rewrite -Hc -Hc' /=. by rewrite -Hl -Hl' /=.
Qed.

Instance add_cpm_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq ==> eq ==> eq ==> @Mvar_eq const_v) add_cpm.
Proof.
  move=> m1 m2 Hm x x' <- {x'} t t' <- {t'} ty ty' <- {ty'} e e' <- {e'}.
  case: x t => //= v [];rewrite ?Hm //.
  by case: e => //= [n | b | [] // sz [] // n ]; rewrite Hm.
Qed.

Instance merge_cpm_m :
  Proper (@Mvar_eq const_v ==> @Mvar_eq const_v ==> @Mvar_eq const_v) merge_cpm.
Proof.
  move=> m1 m2 Hm m1' m2' Hm' z;rewrite /merge_cpm.
  set f :=(X in Mvar.map2 X).
  have Hz : f z None None = None => //.
  have -> := Mvar.map2P m1 m1' Hz.
  have -> := Mvar.map2P m2 m2' Hz.
  by rewrite Hm Hm'.
Qed.

Instance remove_cpm_m :
  Proper (@Mvar_eq const_v ==> Sv.Equal ==> @Mvar_eq const_v) remove_cpm.
Proof.
  move=> m1 m2 Hm s1 s2 Hs z.
  case: Mvar.get (@remove_cpm_spec LO m1 s1 z) => [? |];
   case: Mvar.get (@remove_cpm_spec LO m2 s2 z) => [? |] => //.
  + by rewrite Hm => -[] -> _ [[]] ->.
  + by rewrite Hm Hs => -[ -> | ? ] [].
  by rewrite Hm Hs => -[] -> ? [] .
Qed.

Definition Mvarc_eq T := RelationPairs.RelProd (@Mvar_eq T) (@eq cmd).

Definition Mvarcl_eq T := RelationPairs.RelProd (RelationPairs.RelProd (@Mvar_eq T) (@eq cmd)) (@eq leak_i_tr).

Definition Mvarcls_eq T := RelationPairs.RelProd (RelationPairs.RelProd (@Mvar_eq T) (@eq cmd)) (@eq (seq leak_i_tr)).

Section PROPER.

  Let Pr (i:instr_r) := forall ii m1 m2, Mvar_eq m1 m2 -> Mvarcl_eq (const_prop_ir m1 ii i) (const_prop_ir m2 ii i).

  Let Pi (i:instr) :=
    forall m1 m2, Mvar_eq m1 m2 -> Mvarcl_eq (const_prop_i m1 i) (const_prop_i m2 i).

  Let Pc (c:cmd) :=
    forall m1 m2, Mvar_eq m1 m2 ->
    Mvarcls_eq (const_prop const_prop_i m1 c) (const_prop const_prop_i m2 c).

  Local Lemma Wmk i ii: Pr i -> Pi (MkI ii i).
  Proof. by move=> Hi m1 m2;apply Hi. Qed.

  Local Lemma Wnil : Pc [::].
  Proof. by move=> m1 m2 /= ->. Qed.

  Local Lemma Wcons i c:  Pi i -> Pc c -> Pc (i::c).
  Proof.
    rewrite /Pi /Pc.
    move=> Hi Hc m1 m2 /= Hm.
    move: (Hi m1 m2 Hm).
    case: const_prop_i; move=> [m1' i1'] l1';
    case: const_prop_i; move=> [m2' i2'] l2' [].
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] /= H1 H2 H3 /=. move: (Hc m1' m2' H1).
    case: const_prop; move=> [m1'' c1''] l1'';
    case: const_prop; move=> [m2'' c2''] l2'' [].
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] /= H1' H2' H3'. rewrite /Mvarcls_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. by rewrite /=. rewrite /=. by rewrite -H2 -H2'.
    rewrite /=. by rewrite -H3 -H3'.
   Qed.

  Local Lemma Wasgn x t ty e: Pr (Cassgn x t ty e).
  Proof.
    rewrite /Pr. move=> ii m1 m2 /= Heq.
    have := const_prop_rv_m Heq (refl_equal x).
    case: const_prop_rv; move=> [m1' c1'] l1';
    case: const_prop_rv; move=> [m2'' c2''] l2'' [].
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> H1 ->. case: H1. move=> /= H1 -> /=.
    have := const_prop_e_m Heq (refl_equal e). move=> -> /=.
    case: const_prop_e. move=> e0 l0. rewrite /Mvarcl_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. rewrite /=.
    apply add_cpm_m; auto. auto. auto.
  Qed.

  Local Lemma Wopn xs t o es: Pr (Copn xs t o es).
  Proof.
    rewrite /Pr. move=> ii m1 m2 Heq /=.
    have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs; move=> [m1' c1'] l1';
    case: const_prop_rvs; move=> [m2'' c2''] l2'' [].
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> H1 ->. case: H1. move=> /= H1' /= ->.
    have <- // : [seq const_prop_e m1 i | i <- es] = [seq const_prop_e m2 i | i <- es].
    apply eq_in_map=> x hx. by rewrite Heq.
  Qed.

  Local Lemma Wif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    rewrite /Pc. move=> Hc1 Hc2. rewrite /Pr.
    move=> ii m1 m2 Heq /=.
    have -> : const_prop_e m1 e = const_prop_e m2 e by rewrite Heq.
    case: const_prop_e => b l. case: is_bool =>  [ [] | ].
    + move: (Hc1 m1 m2 Heq). case: const_prop; move=> [m1' c1'] l1';
      case: const_prop; move=> [m2' c2'] l2' [].
      rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
      move=> [] H1 /= -> ->. rewrite /Mvarcl_eq /=.
      rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
      by split.
    + move: (Hc2 m1 m2 Heq). case: const_prop; move=> [m1' c1'] l1';
      case: const_prop; move=> [m2' c2'] l2' [].
      rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
      move=> [] H1 /= -> ->. rewrite /Mvarcl_eq /=.
      rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
      by split. 
    have := Hc1 _ _ Heq; have := Hc2 _ _ Heq.
    case: const_prop; move=> [m1' c1'] l1';
    case: const_prop; move=> [m2' c2'] l2' [] /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] H1 /= -> ->. case: const_prop; move=> [m1'' c1''] l1'';
    case: const_prop; move=> [m2'' c2''] l2'' [] /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] H1' /= -> ->. rewrite /Mvarcl_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. by apply merge_cpm_m. by auto. auto.
  Qed.

  Local Lemma Wfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof.
    rewrite /Pc /Pr. move=> Hc ii m1 m2 Heq /=.
    have -> : const_prop_e m1 lo = const_prop_e m2 lo by rewrite Heq.
    have -> : const_prop_e m1 hi = const_prop_e m2 hi by rewrite Heq.
    case: const_prop_e; move=> lo1 llo1; case: const_prop_e; move=> hi1 lhi1.
    set ww1 := remove_cpm _ _; set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop; move=>[m1' c1'] l1';
    case: const_prop; move=>[m2' c2'] l2' []. 
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] H1 /= -> ->. rewrite /Mvarcl_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. by rewrite /=. by auto. auto.
  Qed.

  Local Lemma Wwhile a c e c': Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    rewrite /Pc /Pr.
    move=> Hc Hc' ii m1 m2 Heq /=.
    set ww1 := remove_cpm _ _;set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc. case: const_prop; move=> [m1' c1'] l1' /=.
    case: const_prop; move=> [m2' c2'] l2' []. 
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] /= H1 /= Hce Hle. move: (Hc' m1' m2' H1).
    case: const_prop; move=> [m1'' c1''] l1'' /=;
    case: const_prop; move=> [m2'' c2''] l2''. rewrite /Mvarcls_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] /= [] H1' /= Hce' Hle'.
    have -> : const_prop_e m1' e = const_prop_e m2' e by rewrite H1.
    case: const_prop_e. move=> a0 l0.
    case: is_bool =>  [ [] | ].
    rewrite /Mvarcl_eq. 
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. rewrite /=. auto. rewrite /=. by rewrite -Hce -Hce'.
    by subst => /=.
    rewrite /Mvarcl_eq /=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. by rewrite /=. auto. auto.
    rewrite /Mvarcl_eq /=. by subst; rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. split. by rewrite /=. rewrite /=. by rewrite -Hce -Hce'.
    by subst. 
  Qed.

  Local Lemma Wcall i xs f es: Pr (Ccall i xs f es).
  Proof.
    rewrite /Pr. move=> ii m1 m2 Heq /=.
    have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs; move=> [m1' c1'] l1' /=.
    case: const_prop_rvs; move=> [m2' c2'] l2' []. 
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    move=> [] /= H1 /= Hce Hle. split => //=.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split. rewrite /=. auto. rewrite /=. rewrite -Hce.
    do 4 f_equal. apply eq_in_map. intro. by rewrite Heq.
    rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    rewrite Hle. do 3 f_equal.
    have <- // : [seq const_prop_e m1 i | i <- es] = [seq const_prop_e m2 i | i <- es].
    apply eq_in_map=> ?. by rewrite Heq.
  Qed.

End PROPER.

Lemma const_prop_i_m :
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarcl_eq const_v) const_prop_i.
Proof.
  move=> m1 m2 Hm i1 i2 <-.
  apply : (instr_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_i_r_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq ==> @Mvarcl_eq const_v) const_prop_ir.
Proof.
  move=> m1 m2 Hm ii1 ii2 <- i1 i2 <-.
  apply : (instr_r_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_m :
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarcls_eq const_v) (const_prop const_prop_i).
Proof.
  move=> m1 m2 Hm c1 c2 <-.
  apply : (cmd_rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall c1) Hm.
Qed.

Lemma valid_cpm_m :
  Proper (eq ==> @Mvar_eq const_v ==> iff) valid_cpm.
Proof.
  move=> s? <- m m' Hm;split => H z n Hget;apply H.
  by rewrite Hm. by rewrite -Hm.
Qed.

Section PROOF.

  Variable p p':prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Variable stk : pointer.
  Notation gd := (p_globs p).

  Hypothesis (p'_def : p' = (const_prop_prog p).1).

  Hypothesis (Fs_def : Fs = (const_prop_prog p).2).

  Hypothesis const_prop_prog_ok : const_prop_prog p = (p', Fs).


  Let Pi s1 i li s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      leak_WF (leak_Fun Fs) (const_prop_i m i).2 li /\
      valid_cpm s2.(evm) ((const_prop_i m i).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' {|emem := emem s1; evm := vm1|} ((const_prop_i m i).1).2 (leak_I (leak_Fun Fs) stk li (const_prop_i m i).2)
                         {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  Let Pi_r s1 i li s2 :=
    forall m ii,
      valid_cpm s1.(evm) m ->
      leak_WF (leak_Fun Fs) (const_prop_ir m ii i).2 li /\
      valid_cpm s2.(evm) ((const_prop_ir m ii i).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' {|emem := emem s1; evm := vm1|} ((const_prop_ir m ii i).1).2 (leak_I (leak_Fun Fs) stk li (const_prop_ir m ii i).2)
                         {|emem := emem s2; evm := vm2|} /\ 
          vm_uincl (evm s2) vm2.

  Let Pc s1 c lc s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      leak_WFs (leak_Fun Fs) (const_prop const_prop_i m c).2 lc /\
      valid_cpm s2.(evm) ((const_prop const_prop_i m c).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' {|emem := emem s1; evm := vm1|} ((const_prop const_prop_i m c).1).2 
                         (leak_Is (leak_I (leak_Fun Fs)) stk (const_prop const_prop_i m c).2 lc)
                         {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  Let Pfor (i:var_i) zs s1 c lf s2 :=
    forall m,
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s1.(evm) m ->
      leak_WFss (leak_Fun Fs) (const_prop const_prop_i m c).2 lf /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem_for p' i zs {|emem := emem s1; evm := vm1|} ((const_prop const_prop_i m c).1).2 
                                (leak_Iss (leak_I (leak_Fun Fs)) stk (const_prop const_prop_i m c).2 lf)
                                {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  Let Pfun m1 fd vargs lf m2 vres :=
    forall vargs',
      List.Forall2 value_uincl vargs vargs' ->
      leak_WFs (leak_Fun Fs) (leak_Fun Fs lf.1) lf.2 /\
      exists vres',
        sem_call p' m1 fd vargs' (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) m2 vres' /\
        List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s m /= ?. split=> //. constructor. split=> //. move=> vm1 Hu1.
    exists vm1;split => //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hi Hpi Hc Hci m /= hvm.
    case heqi : const_prop_i => [mc lti]; case: mc heqi => mi ci heqi. 
    case heqc : const_prop => [mc ltc]; case: mc heqc => mc cc heqc.
    split. rewrite /=. rewrite /Pc in Hci. rewrite /Pi in Hpi.
    move: (Hpi m hvm). rewrite heqi /=. move=> [] Hwf [] hvm2 Hpi'.
    econstructor. apply Hwf. move: (Hci mi hvm2). move=> [] Hwfs' H.
    rewrite heqc /= in Hwfs'. apply Hwfs'.
    move: (Hpi m hvm). rewrite heqi /=. move=> [] Hwf [] hvm2 Hpi'.
    move: (Hci mi hvm2). move=> [] Hwf' [] Hvm' H. split=> //. 
    by rewrite heqc in Hvm'.
    move=>vmi Hm. rewrite /Pi in Hpi. rewrite /Pc in Hci.
    move: (Hpi m hvm). rewrite heqi /=. move=> [] Hwf'' [] hvm' H'.
    move: (H' vmi Hm). move=> [] vm2 [] Hci' Hvm''.
    move: (Hci mi hvm'). rewrite heqc /=. move=> [] Hwf''' [] Hvm3' H''.
    move: (H'' vm2 Hvm''). move=> [] vm3 [] Hci''' Hvm'''.
    exists vm3. split => //.
    by apply sem_app with  {| emem := emem s2; evm := vm2 |}.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof.
    move=> ii i s1 s2 li Hi Hpi.
    rewrite /Pi_r in Hpi. rewrite /Pi. move=> m H.
    move: (Hpi m ii H). move=> [] H' Hvm. split=> //.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
   move=> s1 s2 x tag ty e v v' le lw He Ht Hw m ii Hm.
   have /(_ LO) Hce := const_prop_eP. move: (Hce gd stk e s1 m Hm v le He).
   move=> [] vc [] Hec Hev {Hce}. have /(_ LO) Hcw := const_prop_rvP. 
   move: (Hcw gd stk s1 (s2, lw) m x v').
   case hrv: const_prop_rv => [mx lx]. case: mx hrv => mx x' hrv.
   move=> /= Hwc' {Hcw}. move: (Hwc' Hm Hw). move=> [] Hm' Hwc {Hwc'}.
   case heq: const_prop_e => [me lce]. case hrvq: const_prop_rv=> [mrv lrv].
   case: mrv hrvq => mrv crv hrvq. split. constructor. split=> //.
   + have Hadd /= := @add_cpmP LO. rewrite heq in Hec. rewrite /= in Hec.
     rewrite heq in Hev. rewrite /= in Hev.
     have /= /(_ LO) Hadd':= (@Hadd gd s1 (s2, leak_E stk lx lw) mx x' me tag ty  (vc, leak_E stk lce le) v v' Hec).
     move: (Hadd' Hev Ht Hwc Hm'). move=> H {Hadd} {Hadd'}.
     rewrite hrv in hrvq. case: hrvq => <- <- _. auto. 
   + move=> vm1 hvm1 /=.
     have /(_ LO) := (sem_pexpr_uincl). rewrite heq in Hec. rewrite /= in Hec.
     rewrite heq in Hev. rewrite /= in Hev. move=> Heq. move: (Heq gd s1 vm1 me vc (leak_E stk lce le) hvm1 Hec).
     move=> [] vc' Hec' Hev' {Heq}. move: (truncate_value_uincl).
     move=> Ht'. move:(Ht' ty v vc v' Hev Ht). move=> [] vc'' Htc Hev'' {Ht'}.
     move: (truncate_value_uincl).
     move=> Ht''. move:(Ht'' ty vc vc' vc'' Hev' Htc). move=> [] vc''' Htc' Hev''' {Ht''}.
     move: (value_uincl_trans). move=> Vt. move: (Vt vc'' v' vc''' Hev'' Hev'''). move=> Hev1 {Vt}.
     have /(_ LO) := write_uincl. move=> Hw'. move: (Hw' gd s1 s2 vm1 x' v' vc''' (leak_E stk lx lw) hvm1 Hev1 Hwc).
     move=> [] vm2 Hwc' hvm2 {Hw'}. exists vm2. constructor. apply sem_seq1. constructor.
     apply Eassgn with vc' vc'''. replace (p_globs p') with gd. auto.  by rewrite p'_def /=.
     auto. rewrite hrv in hrvq. case: hrvq => _ <- <-.
     replace (p_globs p') with gd. auto. by rewrite p'_def /=. auto.
    Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es lo H m ii Hm.
    apply: rbindP H=> vs Hes. t_xrbindP.
    move=> [ves les] Ho [sw lw] Hw /= le Hlo Hs Hl.
    have /(_ LO) Hesc := (const_prop_esP). 
    move: (Hesc gd stk es s1 m Hm vs Hes). move=> [] vs' [] Hes' [] Hvc Hlc {Hesc}.
    have /(_ LO) Hwc := const_prop_rvsP. move: (Hwc gd stk s1 sw m xs ves lw).
    case hrvs: const_prop_rvs=> [mc lc]. case: mc hrvs=> mc lv hrvs /=.
    move=> H. move: (H Hm Hw). move=> [] Hmw Hw' {H} {Hwc}. split. constructor.
    split=> //.
    by rewrite -Hs /=. move=> vm1 Hvm1.
    have /(_ LO) Hws := writes_uincl.
    move: (Hws gd s1 sw vm1 lv ves ves (map2 (leak_E stk) lc lw) Hvm1
               (List_Forall2_refl _ value_uincl_refl) Hw').
    move=> [] vm2 Hw'' Hvm2 {Hws}. 
    exists vm2. constructor.
    apply sem_seq1. constructor. constructor. rewrite /sem_sopn /=.
    have /(_ LO) Hesu := (sem_pexprs_uincl).
    move: (Hesu gd s1 vm1 (unzip1 [seq const_prop_e m i | i <- es]) vs' Hvm1 Hes').
    move=> [] vs2 Hes''[]  Hee Hel {Hesu}. rewrite p'_def /=. rewrite Hes'' /=.
    have /(_ LO) Ho' := vuincl_exec_opn_eq. 
    move: (Ho' o (unzip1 vs) (unzip1 vs2) (ves, les) (Forall2_trans value_uincl_trans Hvc Hee) Ho).
    move=> -> {Ho'} /=. rewrite Hw'' /=. rewrite -Hl Hs /=.
    rewrite /= in Hlc. rewrite Hel in Hlc. case: Hlc => -> /=.
    have Hlo' := leak_sopn_eq Hvc Hlo. by have -> /= := leak_sopn_eq Hee Hlo'.
    by rewrite -Hs /=. 
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc He Hs1 Hc1 m ii Hm.
    have  [v' [] ] /= := const_prop_eP stk Hm He.
    case: v' => // b {He} He Hv. rewrite -Hv in He. move=> {Hv} {b}.
    case heq: const_prop_e=> [me lce]. rewrite heq in He. rewrite /= in He.
    case: is_boolP He => b. case: b.
    case hcp: const_prop=> [mc l]. case: mc hcp=> mi ci hcp.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp. move=> [] Hwf [] Hm' {Hc1}.
    move=> H. split. constructor. apply Hwf. split. auto. auto. move=> //.
    case hcp1: const_prop=>[mc1 l1]. case: mc1 hcp1=> mc1 cm1 hcp1.
    case hcp2: const_prop=>[mc2 l2]. case: mc2 hcp2=> mc2 cm2 hcp2.
    split. constructor. rewrite /Pc in Hc1. move: (Hc1 m Hm). move=> [] Hwf Hc.
    rewrite hcp1 in Hwf. apply Hwf. split=> //. apply merge_cpmP; left.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp1. move=> [] Hwf' [] Hm2 {Hc1}.
    move=> H {H}. auto. move=> vm1 Hvm.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp1. move=> [] Hwf'' [] Hm2' H {Hc1}.
    move: (H vm1 Hvm). move=> [] vm2 [] H1 Hvm' {H}. exists vm2. constructor.
    apply sem_seq1. do 2 constructor=> //.
    have /(_ LO) Hee := (sem_pexpr_uincl).
    move: (Hee gd s1 vm1 b (Vbool true) (leak_E stk lce le) Hvm He).
    move=> [] v2 He' /value_uincl_bool1 <- {Hee}.
    replace (p_globs p') with gd. auto. by rewrite p'_def /=. auto.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc He Hs1 Hc1 m ii Hm.
    have  [v' [] ] /= := const_prop_eP stk Hm He.
    case: v' => // b {He} He Hv. rewrite -Hv in He. move=> {Hv} {b}.
    case heq: const_prop_e=> [me lce]. rewrite heq in He. rewrite /= in He.
    case: is_boolP He => b. case: b. move=> //.
    case hcp: const_prop=> [mc l]. case: mc hcp=> mi ci hcp.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp. move=> [] Hm' {Hc1}.
    move=> H. split. constructor. auto. auto. move=> //.
    case hcp1: const_prop=>[mc1 l1]. case: mc1 hcp1=> mc1 cm1 hcp1.
    case hcp2: const_prop=>[mc2 l2]. case: mc2 hcp2=> mc2 cm2 hcp2.
    split. constructor. rewrite /Pc in Hc1. move: (Hc1 m Hm). move=> [] Hws H.
    rewrite hcp2 in Hws. apply Hws. split=> //. apply merge_cpmP; right.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp2. move=> [] Hws [] Hm2 {Hc1}.
    move=> H {H}. auto. move=> vm1 Hvm.
    rewrite /Pc in Hc1. move: (Hc1 m Hm). rewrite hcp2. move=> [] Hws' [] Hm2' H {Hc1}.
    move: (H vm1 Hvm). move=> [] vm2 [] H1 Hvm' {H}. exists vm2. constructor.
    apply sem_seq1. do 2 constructor=> //.
    have /(_ LO) Hee := (sem_pexpr_uincl).
    move: (Hee gd s1 vm1 b (Vbool false) (leak_E stk lce le) Hvm He).
    move=> [] v2 He' /value_uincl_bool1 <- {Hee}.
    replace (p_globs p') with gd. auto. by rewrite p'_def /=. auto.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li Hc1 Hc He Hc1' Hc' Hw1 Hw m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [[m'' c0] lt0] /=.
    case Heq2: const_prop => [[m''' c0'] lt0'] /=.
    have eq1_1 : evm s1 = evm s1 [\ww] by done.
    have /(_ LO) /Hc:= valid_cpm_rm eq1_1 Hm;rewrite -/m' Heq1 /=. 
    move=> [] Hws [] Hm'' Hc0. 
    have := Hc' _ Hm'';rewrite Heq2 /=.
    move=> [] Hws' [] Hvm' Hc0'. 
    have eq1_3 : evm s1 = evm s3 [\ww].
    + rewrite /ww write_i_while -write_c_app;apply: writeP.
      by apply: sem_app;eauto.
    have /(_ LO) /Hw -/(_ ii) /=:= valid_cpm_rm eq1_3 Hm.
    have /(_ LO) H1 := remove_cpm2 m ww.
    have /= : Mvarcls_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile a c e c'))) c)
               (m'', c0, lt0).
    + by have := const_prop_m H1 (refl_equal c); rewrite Heq1.
    case: const_prop  => [[m2'' c2] lt2] [] [].
    rewrite /RelationPairs.RelCompFun /= => Hm2'' -> ->.
    have /= : Mvarcls_eq (const_prop const_prop_i m2'' c') (m''', c0', lt0').
    + by have := const_prop_m Hm2'' (refl_equal c'); rewrite Heq2.
    case heq : const_prop_e => [e' lte]. 
    case: const_prop  => [[m3 c2'] lt2'] [] [].
    rewrite /RelationPairs.RelCompFun /= => _ -> -> -[Hs4 Hrec].
    have heq1 : const_prop_e m2'' e = const_prop_e m'' e.
    + by rewrite Hm2''.
    rewrite -heq1 heq.
    case: (is_bool e' =P Some false) => heqe.
    + have [ vb /= []] := const_prop_eP stk Hm'' He.
      rewrite -heq1 heq /=.
      have ? : e' = false by case: (is_boolP e') (heqe) => [? [->] | ] //.
      by subst e' => /= -[<-].
    move: heqe Hs4 Hrec => /eqP /negbTE -> Hs4 /= [] Hs4' Hrec; split.
    + constructor. auto. rewrite /Pc in Hc'. move: (Hc' m'' Hm'')=> [] Hws'' H.
      rewrite Heq2 in Hws''. auto. apply Hs4. split=> //.
    + by apply (valid_cpm_m (refl_equal (evm s4)) Hm2'').
    move=> vm1 /Hc0 [] vm2 [] hs12 hvm2. 
    move: (hvm2)=> /Hc0' [] vm3 [] hs23 /Hrec [] vm4 [] hs34 hvm4.
    exists vm4; split => //.
    apply:sem_seq1;constructor.
    apply Ewhile_true with {| emem := emem s2; evm := vm2 |} {| emem := emem s3; evm := vm3 |} => //. 
    + have := const_prop_eP stk Hm'' He.
      rewrite -heq1 heq => -[] v' [] hv' /value_uincl_bool1 ?; subst v'.
      replace gd with (p_globs p') in hv'; last by rewrite p'_def.
      by have [ b -> /value_uincl_bool1 -> ] := sem_pexpr_uincl hvm2 hv'.
    have hh := sem_seq1_lis hs34; rewrite hh in hs34.
    by move: hs34 => /sem_seq1_iff hh1; inversion_clear hh1.
  Qed.
  

Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' lc le Hc1 Hc He m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' l0]. case: m'' Heq1=> m'' c0 Heq1 /=.
    case heq: const_prop_e => [me' le'] /=.
    case Heq2: const_prop => [m''' l0']. case: m''' Heq2=> m''' c0' Heq2 /=.
    have eq1_1 : evm s1 = evm s1 [\ww] by done.
    have /(_ LO) /Hc:= valid_cpm_rm eq1_1 Hm;rewrite -/m' Heq1 /=.
    move=> [] Hws -[Hm'' Hc0]. split => //.
    have [v' [Hv' /=]]:= const_prop_eP stk Hm'' He.
    case: v' Hv' => // b Hv' Hvv. rewrite -Hvv in Hv'.
    move=> {Hvv} {b}. rewrite heq in Hv'.
    case:is_boolP Hv' => [ ?[->] //| e0 He0]. auto. move=> Heq.
    + rewrite /=. constructor. auto.
    + rewrite /=. constructor. auto.
    split=> //. 
    have [v' [Hv' /=]]:= const_prop_eP stk Hm'' He.
    case: v' Hv' => // b Hv' Hvv. rewrite -Hvv in Hv'.
    move=> {Hvv} {b}. rewrite heq in Hv'.
    case:is_boolP Hv' => [ ?[->] //| e0 He0]. auto.
    move=> vm1 /Hc0 [vm2 [hsem h]]; exists vm2; split=> //.
    have [v' [Hv' /=]]:= const_prop_eP stk Hm'' He.
    case: v' Hv' => // b' Hv' Hvv. rewrite -Hvv in Hv'.
    move=> {Hvv} {b'}. rewrite heq in Hv'.
    case:is_boolP Hv' => [ ?[->] //| e0 /= He0]. auto.
    apply: sem_seq1;constructor;apply: Ewhile_false => //.
    have /(_ LO) Hee := sem_pexpr_uincl.
    move: (Hee gd s2 vm2 e0 (Vbool false) (leak_E stk le' le) h He0).
    move=> [] v2 He' /value_uincl_bool1 <- {Hee}.
    replace (p_globs p') with gd. auto. by rewrite p'_def /=.
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i r wr c lr lf Hr Hc Hfor m ii Hm /=.
    move: Hr. rewrite /sem_range. case: (r)=> [[d e1] e2] /=.
    t_xrbindP. move=> [ev1 el1] He1 h0 Hi1 [ev2 el2] He2 h4 Hi2 Hwr Hlr.
    set ww := write_i _;set m' := remove_cpm _ _.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    have Heqm: Mvar_eq m' (remove_cpm m' (Sv.union (Sv.singleton i) (write_c c))).
    + by have  /(_ LO) := remove_cpm2 m ww; rewrite /m' /ww write_i_for => ->.
    rewrite /Pfor in Hfor. move: (Hfor m' Heqm Hm'1). move=> Hfor' {Hfor}.
    case heqe1: const_prop_e=> [me1 lc1].
    case heqe2: const_prop_e=> [me2 lc2].
    case Heq1: const_prop => [m'' lc'].
    case: m'' Heq1=> m'' c' Heq1. split.
    + constructor. move: Hfor'. move=> [] Hwfs Hfor'. 
      rewrite Heq1 in Hwfs. apply Hwfs. split.
    + apply: valid_cpm_rm Hm.
      apply (@write_iP _ p  (Cfor i (d, e1, e2) c) s1 s2 (Lfor lr lf)); econstructor.
      rewrite /sem_range. rewrite He1 /=. rewrite He2 /=. rewrite Hi1 /=.
      rewrite Hi2 /=. by rewrite Hwr Hlr /=. auto.
    move: Hfor'=> [] Hwfs Hfor'.
    move=> vm1 /dup[] hvm1 /Hfor' [vm2 [hfor hvm2]]; exists vm2; split=>//.
    apply sem_seq1. constructor. apply Efor with wr. rewrite /=.
    have  /(_ LO) Hce := const_prop_eP. move: (Hce gd stk e1 s1 m Hm ev1 el1 He1).
    move=> [] ev1' [] Hce1 Hev1 {Hce}. rewrite heqe1 in Hce1. rewrite /= in Hce1.
    have  /(_ LO) Hce := const_prop_eP. move: (Hce gd stk e2 s1 m Hm ev2 el2 He2).
    move=> [] ev2' [] Hce2 Hev2 {Hce}. rewrite heqe2 in Hce2. rewrite /= in Hce2.
    have /(_ LO) Hee1 := sem_pexpr_uincl. 
    move: (Hee1 gd s1 vm1 me1 ev1' (leak_E stk lc1 el1) hvm1 Hce1).
    move=> [] ev1'' Hem1 Hv1 {Hee1}.
    have  /(_ LO) Hee2 := sem_pexpr_uincl.
    move: (Hee2 gd s1 vm1 me2 ev2' (leak_E stk lc2 el2) hvm1 Hce2).
    move=> [] ev2'' Hem2 Hv2 {Hee2}.
    replace (p_globs p') with gd. rewrite Hem1 /=. rewrite Hem2 /=.
    rewrite /= in Hev1. rewrite /= in Hev2.
    move: (value_uincl_trans). move=> Ht. move: (Ht ev1' ev1 ev1'' Hev1 Hv1).
    move=> Hev3 {Ht}. move: (value_uincl_int). move=>H1.
    move: (H1 ev1 ev1'' h0 Hev3 Hi1). move=> [] H1' -> {H1}.
    rewrite -H1'. rewrite Hi1 /=.
    move: (value_uincl_trans). move=> Ht. move: (Ht ev2' ev2 ev2'' Hev2 Hv2).
    move=> Hev4 {Ht}. move: (value_uincl_int). move=>H1.
    move: (H1 ev2 ev2'' h4 Hev4 Hi2). move=> [] H2' -> {H1}.
    rewrite -H2'. rewrite Hi2 /=. by rewrite -Hlr Hwr /=. by rewrite p'_def /=.
    rewrite Heq1 in hfor. by rewrite /= in hfor.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c m Hm hv. split. constructor. move=>vm1 hvm1. 
    exists vm1;split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hw Hsemc Hc Hsemf Hf m Heqm Hm.
    have Hm' : valid_cpm (evm s1') m.
    + have Hmi : Mvar_eq m (Mvar.remove m i).
      + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //].
        rewrite Heqm;
        have /(_ LO) := (remove_cpm_spec m (Sv.union (Sv.singleton i) (write_c c)) i).
        by case: Mvar.get => // a [];SvD.fsetdec.
      have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
      by apply: remove_cpm1P Hw Hm.
    have := Hc _ Hm'. move=> [] Hwf [] Hvm2 Hc'.
    split. econstructor. apply Hwf. rewrite /Pfor in Hf. 
    have /(Hf _ Heqm) [Hwfs Hc'']: valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec.
    apply Hwfs.
    move=> vm1 hvm1.
    have /(Hf _ Heqm) [Hwfs Hc'']: valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec.
    have /(_ _ (value_uincl_refl _))[vm1' hw hvm1']:= write_var_uincl hvm1 _ Hw.
    have [vm2 [hc' /Hc'' [vm3 [hfor U]]]]:= Hc' _ hvm1';exists vm3;split => //.
    by apply: EForOne hc' hfor.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hargs Hcall Hfun Hvs m ii' Hm.
    have /(_ LO) Hargs' /= := (const_prop_esP).
    case hlf : lf=> [fn' lfn]. rewrite hlf in Hfun.
    move: (Hargs' gd stk args s1 m Hm vargs Hargs).
    move=> [] vargs' {Hargs'} [] Hargs' [] Hv Hl.
    have /(_ LO) Hvs' := const_prop_rvsP. 
    move: (Hvs' gd stk {| emem := m2; evm := evm s1 |} s2 m xs vs lw).
    case hervs: const_prop_rvs=>[mv lv]; case: mv hervs=> mv cv hervs /=.
    move=> {Hvs'} Hvs'. move: (Hvs' Hm Hvs). move=> {Hvs'} [] Hm2 Hvs' /=.
    split=> //. apply sem_eq_fn in Hcall. rewrite hlf /= in Hcall. 
    rewrite Hcall. apply LT_icallWF. rewrite /Pfun in Hfun. move: (Hfun (unzip1 vargs') Hv).
    move=> [] /= Hwf H. rewrite -Hcall. apply Hwf. split=> //.
    move=> vm1 Hvm1.
    have /(_ LO) Hargs'' := sem_pexprs_uincl.
    move: (Hargs'' gd s1 vm1 (unzip1 [seq const_prop_e m i | i <- args])
                   vargs' Hvm1 Hargs').
    move=> {Hargs''} [] vargs'' Hargs'' [] Hv' Hl'.
    rewrite /Pfun in Hfun.
    have /(_ LO) Hvs'' := writes_uincl. 
    move: (Hfun (unzip1 vargs'') (Forall2_trans value_uincl_trans Hv Hv')).
    move=> {Hfun} [] Hwf [] vres' [] /= Hcall' Hv''.
    move: (Hvs'' gd {| emem := m2; evm := evm s1 |} s2 vm1 cv vs vres'
                 (map2 (leak_E stk) lv lw) Hvm1 Hv'' Hvs').
    move=> {Hvs''} [] vm2 /= Hvs'' Hvm2 /=. exists vm2. split=> //.
    apply sem_seq1. constructor. have /(_ LO) := Ecall.
    replace gd with (p_globs p') in Hargs''. replace gd with (p_globs p') in Hvs''.
    move=> Hrec. 
    move: (Hrec p' {| emem := emem s1; evm := vm1 |} m2
          {| emem := emem s2; evm := vm2 |} ii cv fn
          (unzip1 [seq const_prop_e m i| i <- args])
           vargs'' vres' 
          (fn',leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs fn') lfn)
          (map2 (leak_E stk) lv lw) Hargs'' Hcall' Hvs''). move=> H. rewrite /=.
   case: Hl => <- /=. by rewrite Hl' /=. by rewrite p'_def /=. by rewrite p'_def /=.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hfun htra Hw Hsem Hc Hres Hfull.
    have dcok : map_prog_leak const_prop_fun (p_funcs p) = ((p_funcs p'), Fs).
    + move: const_prop_prog_ok;rewrite /const_prop_prog. by move=> [] <- <- /=.
    move: (get_map_prog_leak dcok Hfun). move=> [] f' [] lt' [] Hf'1 /= Hf'2.
    case: f Hf'1 Hfun htra Hw Hsem Hc Hres Hfull.
    move=> fi fin fp /= c fo fres Hf'1 Hfun htra Hw Hsem Hc Hres Hfull.
    case: f' Hf'1 Hf'2=> ??? c' ? f'_res Hf'1 Hf'2.
    have: valid_cpm (evm s1) empty_cpm. by move=> x n; rewrite Mvar.get0.
    move=> /Hc []; case: const_prop Hf'1=> [[m c''] ltc''] /= heq Hwfs [] hcpm hc' hget vargs1 hargs'.
    have [vargs1' htr hu1]:= mapM2_truncate_val htra hargs'.
    have [vm3 /= hw hu3]:= write_vars_uincl (vm_uincl_refl _) hu1 Hw.
    have [vm4 /= []hc hu4]:= hc' _ hu3.
    have [vres1 hvres1 hu5]:= get_vars_uincl hu4 Hres.
    have [vres1' h1 h2]:= mapM2_truncate_val Hfull hu5.
    split. replace (leak_Fun Fs fn) with ltc''. apply Hwfs.
    rewrite /get_leak in hget. rewrite /leak_Fun. 
    rewrite hget /=.
    by case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    exists vres1';split => //.
    econstructor.
    rewrite /map_prog_leak in dcok. case: dcok => dcok' dcok''. apply Hf'2.
    case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    rewrite /=. rewrite -heq2. apply htr. rewrite /=.
    case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    rewrite -heq3 /=. apply hw.
    case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    rewrite /=. rewrite -heq4. replace (leak_Fun Fs fn) with ltc''.
    apply hc. rewrite /get_leak in hget. rewrite /leak_Fun. by rewrite hget /=.
    case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    rewrite /=. rewrite -heq6. apply hvres1.
    case: heq=> heq1 heq2 heq3 heq4 heq5 heq6 heq7.
    rewrite /=. rewrite -heq5. apply h1.
  Qed.
 
  Lemma const_prop_callP f mem mem' va va' vr lf:
    sem_call p mem f va (f, lf) mem' vr ->
    List.Forall2 value_uincl va va' ->
    leak_WFs (leak_Fun Fs) (leak_Fun Fs f) lf /\
    exists vr', sem_call p' mem f va'(f, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs f) lf)) mem' vr' 
             /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind _ p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) h Hv.
    case: (h va' Hv) => /= Hwfs [] vres' [] h' Hv' {h}; split => //.
    by exists vres'. 
  Qed.

End PROOF.

End Section.
