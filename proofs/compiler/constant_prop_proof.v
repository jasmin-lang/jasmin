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
Require Export constant_prop.

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

Context (gd: glob_decls).

Definition eqok_w (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v -> sem_pexpr gd st e2 = ok v.

(*
Definition array_eq v1 v2 :=
   if type_of_val v1 is sarr _ then v1 = v2 else True.

Lemma array_eq_refl v : array_eq v v.
Proof. by case v => //= -[]. Qed.
Hint Resolve array_eq_refl.

Definition value_uincl_a v1 v2 :=
  value_uincl v1 v2 /\
  array_eq v1 v2.

Lemma value_uincl_a_refl v : value_uincl_a v v.
Proof. done. Qed.
Hint Resolve value_uincl_a_refl.

Lemma of_val_uincl_a ty v1 v2 v1' :
  value_uincl_a v1 v2 ->
  of_val ty v1 = ok v1' ->
  of_val ty v2 = ok v1'.
Proof.
  case: ty v1' => [||n|s] v1' [U Aeq];t_xrbindP.
  + by move=> /(of_val_uincl U) /= [b [-> ]]; rewrite /val_uincl /= => ->.
  + by move=> /(of_val_uincl U) /= [b [-> ]]; rewrite /val_uincl /= => ->.
  + case: v1 v2 U Aeq => //;last by move=> [] //=???;case:ifP.
    by move=> n1 a1 []//= n2 a2 hu /Varr_inj [??];subst.
  by move=> /(of_val_uincl U) /=  /= [w [-> ]] => /andP [_ /eqP ->];rewrite zero_extend_u.
Qed.

Lemma truncate_value_uincl_a ty v1 v2 v1' :
  value_uincl_a v1 v2 ->
  truncate_val ty v1 = ok v1' ->
  truncate_val ty v2 = ok v1'.
Proof.
  by rewrite /truncate_val => U;t_xrbindP => v /(of_val_uincl_a U) -> /= ->.
Qed.
*)

Definition eqok (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v ->
    exists v', sem_pexpr gd st e2 = ok v' /\ value_uincl v.1 v'.1 /\ v.2 = v'.2.

Lemma eqok_weaken e1 e2 st : eqok_w e1 e2 st -> eqok e1 e2 st.
Proof. by move=> h v /h h';exists v. Qed.

Notation "e1 '=[' st ']' e2" := (eqok e1 e2 st)
 (at level 70, no associativity).

Definition eeq_w (e1 e2:pexpr) := forall rho, eqok_w e1 e2 rho.
Definition eeq (e1 e2:pexpr) := forall rho, e1 =[rho] e2.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).


Lemma eeq_w_refl : Reflexive (@eeq_w).
Proof. by move=> ???;eauto. Qed.

Lemma eeq_refl : Reflexive (@eeq).
Proof. by move=> ??? ->;eauto. Qed.

Hint Resolve eeq_refl eeq_w_refl.

Lemma eeq_weaken e1 e2 : eeq_w e1 e2 -> e1 =E e2.
Proof. by move=> h ?;apply eqok_weaken;apply h. Qed.

Definition trans_sem t (vl:value * leak_e) := (vl.1, leak_F t vl.2).

Definition trans_sem_estate t (vl:estate * leak_e) := (vl.1, leak_F t vl.2).

Definition trans_sem_estates t (vl: estate* seq leak_e) := (vl.1, leak_F (LT_seq t) (LSub (vl.2))).

Lemma surj_pairing {T1 T2:Type} (p:T1 * T2) : (p.1,p.2) = p. 
Proof. by case: p. Qed.
Hint Resolve surj_pairing.

Lemma sint_of_wordP s sz e v v' l l': 
sem_pexpr gd s (Papp1 (Oint_of_word sz) e) = ok (v, l) ->
sem_pexpr gd s (sint_of_word sz e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sint_of_word.
case: (is_wconst _ _) (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [ve le] He /= Hw. rewrite /= /sem_sop1 /=.
  t_xrbindP. move=> [yv yl] He' h0 h1 /= Hw1 <- <- Hl' <- Hle /=.
  rewrite He in He'. case: He' => He1 He2. rewrite He1 in Hw. rewrite Hw in Hw1.
  by case: Hw1 => <-.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo /= Ho <- /= Hl /= [yv' yl'] He' vo' /= Ho' <- /= Hl' /=.
  rewrite He in He'. case: He' => H1 H2. rewrite H1 in Ho.
  rewrite Ho in Ho'. by case: Ho' => ->.
Qed.

Lemma sint_of_wordPl sz s e v l:
let e' := (sint_of_word sz e).1 in
let t := (sint_of_word sz e).2 in
sem_pexpr gd s (Papp1 (Oint_of_word sz) e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sint_of_word. rewrite /trans_sem /=.
case: (is_wconst _ _) (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [ve le] He /= Hw. rewrite /= /sem_sop1 /=.
  t_xrbindP. move=> [yv yl] He' h0 h1 /= Hw1 <- <- Hle.
  exists (wunsigned w). split. auto.
  rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw1 in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho <- /= Hl.
  exists vo. rewrite He /=. rewrite Ho /=.
  split. by rewrite Hl /=. auto.
Qed.


Lemma ssign_extendP s sz sz' e v v' l l': 
sem_pexpr gd s (Papp1 (Osignext sz sz') e) = ok (v, l) ->
sem_pexpr gd s (ssign_extend sz sz' e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /ssign_extend.
case: (is_wconst _ _) (@is_wconstP gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v /= ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 /= Hw <- Hv Hl. rewrite wrepr_unsigned.
  move=> Hv' Hl'. rewrite ok_v in He. case: He => He1 He2.
  rewrite -He1 in Hw. rewrite Hw in ok_w. rewrite -Hv -Hv'. by case: ok_w => ->. 
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho <- Hl /= [yv' yl'] He' vo' Ho' <- /= Hl' /=.
  rewrite He in He'. case: He' => H1 H2. rewrite H1 in Ho.
  rewrite Ho in Ho'. by case: Ho' => ->.
Qed.

Lemma ssign_extendPl sz sz' s e v l:
let e' := (ssign_extend sz sz' e).1 in
let t := (ssign_extend sz sz' e).2 in
sem_pexpr gd s (Papp1 (Osignext sz sz') e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /ssign_extend. rewrite /trans_sem.
case: (is_wconst _ _) (@is_wconstP gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v /= ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 /= Hw Hv <- Hl /=. rewrite wrepr_unsigned.
  exists (Vword (sign_extend sz w)). split. auto. rewrite -Hv.
  rewrite ok_v in He. case: He => He1 _. rewrite He1 in ok_w.
  rewrite ok_w in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho <- /= Hl /=.
  exists vo. rewrite He /=.
  rewrite Ho /=. by rewrite Hl.
Qed.

Lemma szero_extendP s sz sz' e v v' l l': 
sem_pexpr gd s (Papp1 (Ozeroext sz sz') e) = ok (v, l) ->
sem_pexpr gd s (szero_extend sz sz' e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /szero_extend.
case: (is_wconst _ _) (@is_wconstP gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 Hw Hv Hvv Hl. rewrite wrepr_unsigned.
  move=> Hv' Hl'. rewrite Hvv in Hv. rewrite -Hv. rewrite -Hv'.
  rewrite ok_v in He. case: He => He1 _. rewrite He1 in ok_w.
  rewrite ok_w in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho <- Hl /= [yv' yl'] He' vo' Ho' <- /= Hl' /=.
  rewrite He in He'. case: He' => H1 H2. rewrite H1 in Ho.
  rewrite Ho in Ho'. by case: Ho' => ->.
Qed.

Lemma szero_extendPl sz sz' s e v l:
let e' := (szero_extend sz sz' e).1 in
let t := (szero_extend sz sz' e).2 in
sem_pexpr gd s (Papp1 (Ozeroext sz sz') e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /szero_extend. rewrite /trans_sem.
case: (is_wconst _ _) (@is_wconstP gd s sz' e).
+ move => w /(_ _ erefl). t_xrbindP. move => [yv yl] ok_v ok_w /=.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> [yv' yl'] He h0 h1 Hw Hv Hvv Hl /=. rewrite wrepr_unsigned.
  exists (Vword (zero_extend sz w)). split. auto. rewrite Hvv in Hv. rewrite -Hv.
  rewrite ok_v in He. case: He => He1 _. rewrite He1 in ok_w.
  rewrite ok_w in Hw. by case: Hw => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He vo Ho <- /= Hl /=.
  exists vo. rewrite He /=.
  rewrite Ho /=. by rewrite Hl.
Qed.

Lemma snot_boolP s e v l v' l': 
sem_pexpr gd s (Papp1 Onot e) = ok (v, l) ->
sem_pexpr gd s (snot_bool e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
case: e=> //= ;try auto.
+ by move=> b [] <- Hl [] <- Hle.
+ move=> x. t_xrbindP.
  move=> [yv yl] h Hg [] Hv1 Hv2. rewrite /sem_sop1 /=.
  t_xrbindP. move=> h0 y Hb Hv' Hv'' Hl [yv' yl'] h6
  Hg' [] Hl1 Hl2 h9 h10 Hb' He' Hv3 Hl1'.
  rewrite Hg in Hg'. case: Hg' => Hg1. rewrite -Hv1 Hg1 in Hb.
  rewrite -Hl1 Hb in Hb'. rewrite Hv'' in Hv'.
  rewrite Hv3 in He'. case: Hb' => Hb''. rewrite Hb'' in Hv'.
  by rewrite -He' -Hv'.
+ move=> g. t_xrbindP.
  move=> [yv yl] vg Hg [] <- Heyl. rewrite /sem_sop1 /=.
  t_xrbindP. move=> vb b Hb Heb Hv Hl.
  rewrite Hg /=. move=> [yv' yl'] vv [] Hg' [] Hvv Hyl.
  rewrite -Hvv -Hg' Hb /=. move=> bv hb [] Hb' Hbv' Hv' Hl'.
  rewrite Hv' in Hbv'. rewrite Hv Hb' in Heb. by rewrite -Hbv' -Heb.
+ move=> w v0 e. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi w' Ha Hv Hl. 
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> vb b Hb Heb <- Hel /=. rewrite He /=.
  move=> h [h4 h5] [] <- <-. rewrite Hi /= => h7 [] <-.
  rewrite Ha /=. move=> h9 [] <-. rewrite Hv /= => [] <- /=.
  rewrite Hb /= => h' h'' [] Hb' Hve Hv' Hl'.
  rewrite -Heb. rewrite -Hve -Hb' in Hv'. by rewrite -Hv'.
+ move=> w x e. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh Hhv Hyl.
  rewrite Hg /= => [hv hl] h6 [] <-. rewrite Hp /= => [] Hev.
  rewrite He /= => h10 [] <- /=. rewrite Hp' /= => h12 [] <-.
  case: Hev => <-. rewrite Hr /= => wr [] <-; rewrite He' /= => <-.
  rewrite Hb /=. move=> h17 h18 => [] Hb1 Hb2 <- Hl'.
  rewrite Hhv in Hh; rewrite -Hh. case: Hb1 => ->. by rewrite Hb2.
+ move=> s0 e. t_xrbindP.
  move=> h [yv yl] He /= h1 Ho <-. rewrite /sem_sop1 /=.
  t_xrbindP => h0 y /to_boolI ????; subst.
  case hop: (if s0 is Onot then false else true).
  * move => eval.
    have {eval} : sem_pexpr gd s (Papp1 Onot (Papp1 s0 e), LT_id).1 = ok (v', l') by case: s0 hop eval {Ho}.
    by rewrite /= He /= Ho /= /sem_sop1 /= => - [<- _].
  case: s0 hop Ho => // _; rewrite /sem_sop1 /= He; t_xrbindP => ? /to_boolI -> <- <- _.
  by rewrite negbK.
+ move=> s0 e e0. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 Hs2 Hev v1 Hs1 Hev' Hl'.
  rewrite He /=. rewrite He0 /=. move=> h10 h11 [] <- h13 [] <-.
  rewrite Hs2 /=. move=> h15 [] <-. rewrite Hev /= => <-.
  rewrite Hs1 /=. move=> H18 [] <- <- _. by rewrite Hev'.
+ move=> o l0. t_xrbindP. move=> [yv yl] h Hm h1 H Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hb Hh <- Hl'. rewrite Hm /=.
  move=> h6 h7 [] <-. rewrite H /=. move=> h9 [] <-.
  rewrite Hl /= => <- /=. rewrite Hb /=. move=> h12 h13 [] <- <- <- _.
  by rewrite Hh.
+ move=> ty e e0 e1. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh <- Hl. rewrite He /= => h5 h6 [] <-.
  rewrite Hb /=. rewrite He0 He1 /= => h10 [] <- h12 [] <- h14 [] <-.
  rewrite Ht Ht1 /= => h16 [] <- h18 [] <-. rewrite Hif /= => <-.
  rewrite Hb' /= => h21 h22 [] <- <- <- _. by rewrite -Hh.
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
+ move=> b [] <- Hl. by exists (~~b).
+ move=> x. t_xrbindP.
  move=> [yv yl] h Hg [] Hv1 Hv2. rewrite /sem_sop1 /=.
  t_xrbindP. move=> h0 y Hb Hv' Hv'' Hl. rewrite Hg /=. rewrite -Hv1 in Hb.
  rewrite Hb /=. rewrite Hl in Hv2. rewrite -Hv2. rewrite -Hv' in Hv''.
  rewrite -Hv''. by exists (~~y).
+ move=> g. t_xrbindP.
  move=> [yv yl] vg Hg [] <- Heyl. rewrite /sem_sop1 /=.
  t_xrbindP. move=> vb b Hb Heb Hv Hl.
  rewrite Hg /=. rewrite Hb /=. rewrite -Heb in Hv.
  rewrite -Hv. rewrite -Heyl in Hl. rewrite -Hl.
  by exists (~~ b).
+ move=> w v0 e. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi w' Ha Hv Hl. 
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> vb b Hb /= Heb <- Hel /=. rewrite He /=.
  rewrite Hi /=. rewrite -Hv in Hb. rewrite /= in Hb. rewrite Ha /=.
  exists (~~b). rewrite -Heb. split. inversion Hb. auto.
+ move=> w x e. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh Hhv Hyl.
  rewrite Hg /=. rewrite Hp /=. rewrite He /=. rewrite Hp' /=.
  rewrite Hr /=. case: He' => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. rewrite Hhv in Hh. exists (~~ b). rewrite -Hh.
  inversion Hb.
+ move=> s0 e. t_xrbindP.
  move=> h [yv yl] He /= h1 Ho <-. rewrite /sem_sop1 /=.
  t_xrbindP => h0 y /to_boolI Hy hh0 Hv Hl; subst.
  case hop: (if s0 is Onot then false else true).
    have eval : sem_pexpr gd s (Papp1 Onot (Papp1 s0 e), LT_id).1 = ok (Vbool (~~y), l).
    by rewrite /= He /= Ho /=. admit. admit.
+ move=> s0 e e0. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 /= Hs2 /= Hev v1 Hs1 <- Hl'.
  rewrite He /=. rewrite He0 /=. rewrite Hs2 /=. rewrite -Hev in Hs1.
  rewrite Hs1 /=. rewrite -Hev in Hl'. rewrite -Hl' /=.
  by exists v1.
+ move=> o l0. t_xrbindP. move=> [yv yl] h Hm h1 H Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hb Hh <- Hl'. rewrite Hm /=.
  rewrite H /=. case: Hl=> Hl1 Hl2. rewrite -Hl1 in Hb. rewrite Hb /=.
  rewrite Hh. rewrite Hl' in Hl2. rewrite -Hl2. by exists h0.
+ move=> ty e e0 e1. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh <- Hl.
  rewrite He /=. rewrite Hb /=. rewrite He0 He1 /=.
  rewrite Ht Ht1 /=. rewrite -Hif in Hb'. rewrite /= in Hb'.
  rewrite Hb' /=. rewrite Hh. rewrite -Hif in Hl. rewrite /= in Hl.
  rewrite -Hl. by exists h.
Admitted.
 
Lemma snot_wP s sz e v v' l l': 
sem_pexpr gd s (Papp1 (Olnot sz) e) = ok (v, l) ->
sem_pexpr gd s (snot_w sz e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /snot_w.
case: is_wconst (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [yv yl] He Hw. rewrite /sem_sop1 /= wrepr_unsigned.
  t_xrbindP. move=> [yv' yl'] He'. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' Hh <- Hhl Hv' Hl'.
  rewrite -Hh -Hv'. rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw in Hw'. by case: Hw' => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- <- _ [yv' yl'] He' h6 h7 Hw' <- <- _.
  rewrite He in He'. case: He' => He1 He2. rewrite He1 in Hw.
  rewrite Hw in Hw'. by case: Hw' => <-.
Qed.

Lemma snot_wPl sz s e v l:
let e' := (snot_w sz e).1 in
let t := (snot_w sz e).2 in
sem_pexpr gd s (Papp1 (Olnot sz) e)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /snot_w. rewrite /trans_sem.
case: is_wconst (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl). t_xrbindP.
  move=> [yv yl] He Hw /=. rewrite /sem_sop1 /= wrepr_unsigned.
  t_xrbindP. move=> [yv' yl'] He'. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' <- <- Hhl.
  exists (Vword (wnot w)). split. auto.
  rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw in Hw'. by case: Hw' => ->.
+ move=> _ /=. t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- <- <-. rewrite He /=. rewrite Hw /=.
  exists (Vword (wnot y)). by split.
Qed.

Lemma sneg_intP s e v v' l l': 
sem_pexpr gd s (Papp1 (Oneg Op_int) e) = ok (v, l) ->
sem_pexpr gd s (sneg_int e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
case: e => //.
+ by move=> z /= [] <- -> [] <- _.
+ move=> x /=. t_xrbindP.
  move=> [yv yl] h Hg Hh. rewrite /sem_sop1 /=.
  t_xrbindP. move=> h0 y Hi Hh0 <- _. rewrite Hg /=.
  move=> [yv' yl'] h6 [] <- [] <-. case: Hh => Hh1 Hh2.
  rewrite -Hh1 in Hi. rewrite Hi /=. move=> _ h9 h10 [] <- <-.
  move=> <- _. by rewrite Hh0.
+ move=> g /=. t_xrbindP.
  move=> [yv yl] h Hg h2. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hi <- <- _ h6 h7. rewrite Hg /=.
  move=> [] <- <- h10 h11. case: h2 => h21 h22.
  rewrite -h21 in Hi. by rewrite Hi /= => [] [] <- <- <- _.
+ move=> sz x e /=. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi h2 Ha Hv Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hi' <- <- Hl'. rewrite He /= => h5 h6 [] <-.
  rewrite Hi /= => h8 [] <-. rewrite Ha /= => h10 [] <- <-.
  rewrite Hv. by rewrite Hi' /= => h13 h14 [] <- <- <- _.
+ move=> w x e /=. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh Hhv Hyl.
  rewrite Hg /= => [hv hl] h6 [] <-. rewrite Hp /= => [] Hev.
  rewrite He /= => h10 [] <- /=. rewrite Hp' /= => h12 [] <-.
  case: Hev => <-. rewrite Hr /= => wr [] <-; rewrite He' /= => <-.
  rewrite Hb /=. move=> h17 h18 => [] Hb1 Hb2 <- Hl'.
  rewrite Hhv in Hh; rewrite -Hh. case: Hb1 => ->. by rewrite Hb2.
+ move => op e /=; t_xrbindP => _ [??] he ? hop <-.
  rewrite /sem_sop1 /=; t_xrbindP => ?? /to_intI ???? H; subst.
  case k: (if op is Oneg Op_int then false else true).
  * have {H} : sem_pexpr gd s (Papp1 (Oneg Op_int) (Papp1 op e)) = ok (v', l') by case: (op) k H => // - [].
    by rewrite /= he /= hop => - [<- _].
  case: op k hop H => // - [] // _.
  rewrite /sem_sop1 he /=; t_xrbindP => ? /to_intI -> <- <- _; exact: Z.opp_involutive.
+ move=> s0 e e0 /=. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 Hs2 Hev v1 Hs1 Hev' Hl'.
  rewrite He /=. rewrite He0 /=. move=> h10 h11 [] <- h13 [] <-.
  rewrite Hs2 /=. move=> h15 [] <-. rewrite Hev /= => <-.
  rewrite Hs1 /=. move=> H18 [] <- <- _. by rewrite Hev'.
+ move=> o l0 /=. t_xrbindP. move=> [yv yl] h Hm h1 H Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hb Hh <- Hl'. rewrite Hm /=.
  move=> h6 h7 [] <-. rewrite H /=. move=> h9 [] <-.
  rewrite Hl /= => <- /=. rewrite Hb /=. move=> h12 h13 [] <- <- <- _.
  by rewrite Hh.
+ move=> ty e e0 e1 /=. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh <- Hl. rewrite He /= => h5 h6 [] <-.
  rewrite Hb /=. rewrite He0 He1 /= => h10 [] <- h12 [] <- h14 [] <-.
  rewrite Ht Ht1 /= => h16 [] <- h18 [] <-. rewrite Hif /= => <-.
  rewrite Hb' /= => h21 h22 [] <- <- <- _. by rewrite -Hh.
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
  t_xrbindP. move=> h0 y Hi <- <- <-. rewrite Hg /=.
  case: Hh => -> <-. rewrite Hi /=. by exists (-y)%Z.
+ move=> g /=. t_xrbindP.
  move=> [yv yl] h Hg h2. rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hi <- <- <-. rewrite Hg /=.
  case: h2 => h2v <-. rewrite h2v. rewrite Hi /=.
  by exists (-y)%Z.
+ move=> sz x e /=. t_xrbindP. move=> [yv yl].
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=.
  t_xrbindP. move=> [yv' yl'] He z Hi h2 Ha Hv Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hi' <- <- Hl'. rewrite He /=. rewrite Hi /=.
  rewrite -Hv in Hi'. rewrite /= in Hi'. inversion Hi'.
+ move=> w x e /=. t_xrbindP.
  move=> [yv yl] h v0 Hg Hp [yv' yl'] He h' Hp' w' Hr He' /=.
  rewrite /sem_sop1 /=. t_xrbindP. move=> bv b Hb Hh Hhv Hyl.
  rewrite Hg /=. rewrite Hp /=. rewrite He /=. rewrite Hp' /=.
  rewrite Hr /=. case: He' => He1' He2'. rewrite -He1' in Hb.
  inversion Hb.
+ move => op e /=; t_xrbindP => _ [yv yl] he vo hop <-.
  rewrite /sem_sop1 /=; t_xrbindP => h y /to_intI h1 h2 h3 h4; subst.
  case k: (if op is Oneg Op_int then false else true).
  * have H : sem_pexpr gd s (Papp1 (Oneg Op_int) (Papp1 op e)) = ok (Vint (-y)%Z, l).
    rewrite /=. rewrite he /=. by rewrite hop /=.
  admit. admit.
+ move=> s0 e e0 /=. t_xrbindP.
  move=> y [yv yl] He [yv' yl'] He0 v0 Hs2 Hev v1 Hs1 Hev' Hl'.
  rewrite He /=. rewrite He0 /=.
  rewrite Hs2 /=. rewrite -Hev in Hl'. rewrite /= in Hl'.
  rewrite -Hev in Hs1. rewrite /= in Hs1. rewrite Hs1 /=. rewrite Hev' -Hl'. by exists v.
+ move=> o l0 /=. t_xrbindP. move=> [yv yl] h Hm h1 H Hl.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h0 y Hb Hh <- Hl'. rewrite Hm /=.
  rewrite H /=. case: Hl => Hl1 Hl2. rewrite -Hl1 in Hb.
  rewrite Hb /=. rewrite Hh. rewrite Hl' in Hl2.
  rewrite -Hl2 /=. by exists h0.
+ move=> ty e e0 e1 /=. t_xrbindP.
  move=> y [yv yl] He h1 Hb [y0 l0] He0 [y1 l1] He1 h7 Ht h9 Ht1 /= Hif.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y2 Hb' Hh <- Hl. rewrite He /=.
  rewrite Hb /=. rewrite He0 He1 /=.
  rewrite Ht Ht1 /=. rewrite -Hif in Hb'. rewrite /= in Hb'.
  rewrite Hb' /=. rewrite -Hif in Hl. rewrite -Hl /=.
  rewrite Hh. by exists h.
Admitted.

Lemma sneg_wP s sz e v v' l l': 
sem_pexpr gd s (Papp1 (Oneg (Op_w sz)) e) = ok (v, l) ->
sem_pexpr gd s (sneg_w sz e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sneg_w.
case: is_wconst (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl) /=. t_xrbindP.
  move=> [yv yl] He Hw [yv' yl'] He'.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' <- <- _ <- _.
  rewrite wrepr_unsigned.
  rewrite He in He'. case: He' => He1' He2'.
  rewrite He1' in Hw. rewrite Hw in Hw'.
  by case: Hw' => ->.
+ move=> _ /=. t_xrbindP. move=> [yv yl] He.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- <- _. rewrite He /= => h4 [] <-.
  by rewrite Hw /= => h6 h7 [] <- <- <- _.
Qed.

Lemma sneg_wPl sz s e v l:
let e' := (sneg_w sz e).1 in
let t := (sneg_w sz e).2 in
sem_pexpr gd s (Papp1 (Oneg (Op_w sz)) e) = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /sneg_w. rewrite /trans_sem.
case: is_wconst (@is_wconstP gd s sz e).
+ move => w /(_ _ erefl) /=. t_xrbindP.
  move=> [yv yl] He Hw [yv' yl'] He'.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw' <- <- Hl. rewrite wrepr_unsigned.
  exists (Vword (- w)). rewrite He in He'.
  case: He' => He1' He2'. rewrite He1' in Hw.
  rewrite Hw in Hw'. by case: Hw' => ->.
+ move=> _ /=. t_xrbindP. move=> [yv yl] He.
  rewrite /sem_sop1 /=. t_xrbindP.
  move=> h y Hw <- <- <-. rewrite He /=.
  rewrite Hw /=. exists (Vword (-y)).
  by split.
Qed.

Lemma s_op1P s o e v v' l l': 
sem_pexpr gd s (Papp1 o e) = ok (v, l) ->
sem_pexpr gd s (s_op1 o e).1 = ok (v', l') ->
value_uincl v v'.
Proof.
case: o => [w|w|w w0|w w0||w|[|o]];
eauto using sint_of_wordP, ssign_extendP, szero_extendP,
snot_boolP, snot_wP, sneg_intP, sneg_wP. rewrite /=.
t_xrbindP. move=> [yv yl] He. rewrite /sem_sop1 /=. t_xrbindP.
move=> h y Hi Hh <- Hl h4 He'. rewrite He in He'.
case: He' => <- He2. rewrite Hi /= => // h7 [] <- <-.
rewrite Hh. by move=> <- _.
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

Lemma sandP s e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 Oand e1 e2) = ok (v, l) ->
sem_pexpr gd s (sand e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sand.
case: is_boolP => [b1 /=| {e1} e1].
+ t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop2 /=. case: b1.
  - t_xrbindP. move=> h y /to_boolI <- <- <- _ He'. rewrite He in He'.
    by case: He' => <- _.
  t_xrbindP. move=> h y Hb <- <- Hl /= He' /=.
  by case: He' => <- _.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y Hb <- <- _ He'. rewrite He in He'.
    apply to_boolI in Hb. case: He' => <- _. rewrite Hb.
    by rewrite andbT.
  t_xrbindP. move=> h y /to_boolI Hy <- <- _ /= He'.
  case: He' => <- _. by rewrite andbF.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- <- _.
  rewrite He1 He2 /=. move=> h6 [] <- h8 [] <-. rewrite Hb1 Hb2.
  by move=> h10 h11 [] <- h13 [] <- <- <- _.
Qed.

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
  - t_xrbindP. move=> h y /to_boolI <- <- <- <-.
    exists yv.
    split. simpl. auto. by rewrite /=. auto.
  t_xrbindP. move=> h y /to_boolI H <- <- <-. exists false.
  split. by rewrite /=. by rewrite /=.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y /to_boolI H. move=> <- <- <-. exists yv.
    rewrite He. split. auto. rewrite H /=. by rewrite andbT.
  t_xrbindP. move=> h y /to_boolI Hy <- <- <- /=.
  exists false. split. auto. by rewrite andbF.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- <- <-.
  rewrite He1 He2 /=. rewrite Hb1 Hb2 /=. exists (y && h1).
  split. auto. auto.
Qed.

Lemma sorP s e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 Oor e1 e2) = ok (v, l) ->
sem_pexpr gd s (sor e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sor.
case: is_boolP => [b1 /=| {e1} e1].
+ t_xrbindP.
  move=> [yv yl] He. rewrite /sem_sop2 /=. case: b1.
  - t_xrbindP. move=> h y /to_boolI H <- <- _ He'. rewrite /= in He'.
    by case: He' => <- _.
  t_xrbindP. move=> h y /to_boolI <- <- <- _ He' /=. rewrite He in He'.
  by case: He' => <- _.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y /to_boolI H <- <- _ He'.
    rewrite /= in He'. case : He' => <- _. by rewrite orbT. 
  t_xrbindP. move=> h y /to_boolI Hy <- <- _ /= He'. rewrite He in He'.
  case: He' => <- _. rewrite orbF. by rewrite Hy.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- <- _.
  rewrite He1 He2 /=. move=> h6 [] <- h8 [] <-. rewrite Hb1 Hb2 /=.
  by move=> h10 h11 [] <- h13 [] <- <- <- _.
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
  - t_xrbindP. move=> h y /to_boolI H <- <- <-.
    exists true.
    split. simpl. auto. by rewrite /=.
  t_xrbindP. move=> h y /to_boolI <- <- <- <-. exists yv.
  split. by rewrite /=. by rewrite /=.
case: is_boolP => [b2 /=| {e2} e2].
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=. case: b2.
  - t_xrbindP. move=> h y /to_boolI H. move=> <- <- <-. exists true.
    rewrite /=. split. auto. rewrite /=. by rewrite orbT.
  t_xrbindP. move=> h y /to_boolI Hy <- <- <- /=.
  exists yv. split. auto. rewrite Hy.
  by rewrite orbF.
+ rewrite /=. t_xrbindP. move=> [yv1 yl1] He1 [yv2 yl2] He2.
  rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hb1 h1 Hb2 <- <- <-.
  rewrite He1 He2 /=. rewrite Hb1 Hb2 /=. exists (y || h1).
  split. auto. auto.
Qed.

Lemma sadd_intP s e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oadd Op_int) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sadd_int e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sadd_int.
case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] //=.
+ t_xrbindP. by move=> <- _ <- _.
+ t_xrbindP. move=> [v2 l2] Hv2; rewrite /sem_sop2 /=.
  t_xrbindP. move=> h z2 /of_val_int /= H <- <- _ /=.
  subst v2. case: eqP => [-> // | /= _]. by rewrite Hv2 /= => [] [] <- _.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h0 z1 /of_val_int /= H <- <- _. rewrite H in He.
  rewrite Hv2 in He. by case: He => <- _.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h z /of_val_int /= H <- <- _. rewrite H in He.
  case: eqP => [-> // | /= _]. rewrite He /= => [] [] <- _ /=.
  by rewrite Z.add_0_r.
+ t_xrbindP. rewrite /sem_sop2 /=.
  t_xrbindP. move=> [yv' yl'] He' h2 zo /of_val_int /= Hi <- <- _.
  rewrite Hi in He'. rewrite He in He'. by case: He'=> -> _.
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> [yv' yl'] He2.
  move=> h1 y /of_val_int Hi h3 /of_val_int /= Hi' /=.
  rewrite Hi in He1. rewrite Hi' in He2. move=> <- <- _.
  move=> [y1 l1] He1' [y2 l2] He2'. move=> h12 h13 /of_val_int H13.
  move=> h15 /of_val_int H10. rewrite /= in H13.
  rewrite /= in H10. rewrite H10 in He2'. move=> <- <- _.
  rewrite He1 in He1'. rewrite He2 in He2'. rewrite H13 in He1'.
  case: He1' => <- _. by case: He2' => -> _.
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
  t_xrbindP. move=> h z2 /of_val_int /= H <- <- <- /=.
  subst v2. case: eqP => [-> // | /= _]. exists z2.
  split. auto. by rewrite /=.
+ exists (n1 + z2)%Z.
  rewrite /sem_sop2 /=. rewrite Hv2 /=. by split.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h z /of_val_int /= H <- <- <-. rewrite H in He.
  case: eqP => [-> // | /= _]. exists z.
  split. auto. rewrite /=. by rewrite Z.add_0_r.
+ exists (z + n2)%Z.
  rewrite /sem_sop2 /=. rewrite He /=. by split.
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> [yv' yl'] He2.
  move=> h1 y /of_val_int Hi h3 /of_val_int /= Hi' /=.
  rewrite Hi in He1. rewrite Hi' in He2. move=> <- <- <-.
  rewrite He1 He2 /=. exists (y + h3)%Z. by split.
Qed.

(*Check value_uincl_zero_ext.
Lemma value_uincl_a_zero_ext (sz sz' : wsize) (w' : word sz'):
  (sz ≤ sz')%CMP → value_uincl_a (Vword (zero_extend sz w')) (Vword w').
Proof. by move=> hle;split;first by apply value_uincl_zero_ext. Qed.
*)
Local Hint Resolve value_uincl_zero_ext.

Lemma sadd_wP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oadd (Op_w sz)) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sadd_w sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sadd_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He' /=. move=> h4.
  rewrite /sem_sop2 /=. t_xrbindP. move=> y Hw h3 Hw' <- <- _ <- _.
  have := is_wconstP gd s h1; have := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2.
  rewrite He /=. move=> Hw2. move=> h5 [] <- /=. rewrite Hw /=.
  move=> [] ->. rewrite He' in He2. case: He2 => He21 He22.
  rewrite He21 in Hw'. rewrite Hw2 in Hw'. case: Hw' => ->.
  by rewrite wrepr_unsigned.
+ case: eqP => hz.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. have := is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> [yv1 yl1] [] -> -> -> h3 h4 [] <-.
    rewrite He2 /=. move=> h6 Hv.
    apply of_val_word in Hv. move: Hv. move=> [] sz' [] w' [] Hsz' -> ->.
    move=> <- <- Hl [] <- Hl' /=.
    rewrite hz /=. rewrite GRing.add0r /=. rewrite /word_uincl /zero_extend.
    by rewrite Hsz' /=.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- _.
    rewrite He1 /=. move=> h8 [] <-. rewrite He2 /=. move=> h10 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite Hw /=. move=> h12 h13 [] <-. rewrite Hw' /=. by move=> h15 [] <- <- <- _.
+ case: eqP => // hz /=. 
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have:= is_wconstP gd s h2.
    rewrite He' /=. move=> -> /=.
    rewrite He /=. move=> h y Hw'.
    apply of_val_word in Hw'. move: Hw'. move=> [] sz' [] x0 [] Hsz -> -> h3 [] <- <- <- Hl.
    move=> [] <- Hl'. rewrite hz /=. rewrite GRing.addr0. rewrite /word_uincl /zero_extend.
    by rewrite Hsz /=.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- _.
    rewrite He1 /=. move=> h8 [] <-. rewrite He2 /=. move=> h10 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite Hw /=. move=> h12 h13 [] <-. rewrite Hw' /=. by move=> h15 [] <- <- <- _.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- <- _. rewrite He1 /=. move=> [yv1 yl1] [] <- _.
  rewrite He2 /=. move=> [yv2 yl2] [] <- _. rewrite Hw Hw' /=. 
  by move=> h12 h13 [] <- h15 [] <- <- <- _.
Qed.

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
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He' /=. move=> h4.
  rewrite /sem_sop2 /=. t_xrbindP. move=> y Hw h3 Hw' <- <- _.
  rewrite wrepr_unsigned. exists (Vword (n1+n2)).
  have := is_wconstP gd s h1; have := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2.
  rewrite He2 in He'. case: He' => -> He2'. rewrite Hw' /=.
  move=> [] <-. rewrite He /=. move=> [yv1' yl1'] [] <- Hl'.
  rewrite Hw /=. by move=> [] <-.
+ case: eqP => hz.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. have := is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> [yv1 yl1] [] <- Hl -> h3 h4 [] <- h6 Hv.
    move=> <- <- Hl'. rewrite He2 /=.
    apply of_val_word in Hv. move: Hv. move=> [] sz' [] w' [] Hsz' -> ->.
    rewrite hz /=. rewrite GRing.add0r /=.
    rewrite /word_uincl /zero_extend. exists (Vword w'). rewrite Hsz'.
    by rewrite -Hl' /=.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- <-.
    rewrite He1 /=. exists (Vword (y + h3)).
    rewrite He2 /=. rewrite /sem_sop2 /=.
    rewrite Hw /=. rewrite Hw' /=. by split.
+ case: eqP => // hz /=. 
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have:= is_wconstP gd s h2.
    rewrite He' /=. move=> -> h y Hw'. move=> h3 [] <- <- <- <- /=.
    rewrite He /=. exists yv.
    apply of_val_word in Hw'. move: Hw'. move=> [] sz' [] x0 [] Hsz -> ->.
    rewrite hz /=. rewrite GRing.addr0. rewrite /word_uincl /zero_extend.
    rewrite Hsz. by rewrite andTb.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- <-.
    rewrite He1 /=. rewrite He2 /=.
    rewrite Hw /=. rewrite Hw' /=. exists (Vword (y+h3)).
    by split.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- <- <-. rewrite He1 /=.
  rewrite He2 /=. rewrite Hw Hw' /=. exists (Vword (y + h3)). by split.
Qed.

Lemma saddP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oadd ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sadd ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
by case: ty; eauto using sadd_intP, sadd_wP.
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

Lemma ssub_intP s e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Osub Op_int) e1 e2) = ok (v, l) ->
sem_pexpr gd s (ssub_int e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /ssub_int.
case: (is_constP e1) => [n1 | {e1} e1];
case: (is_constP e2) => [n2 | {e2} e2] // /=.
+ move=> H1 H2.  case: H1 => <- _. by case: H2 => <- _.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hy <- <- _.
  move=> [yv' yl'] He'. move=> h6 h7 /of_val_int /= Hy' /= <- <- _ .
  rewrite He in He'. rewrite Hy in He'. rewrite Hy' in He'.
  by case: He' => <- _.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int /= Hy <- <- _.
  case: eqP.
  - move=> Hn2 He'. rewrite He in He'. rewrite Hy in He'.
    rewrite Hn2. case: He' => <- _. by rewrite Z.sub_0_r.
  move=> Hn2 /=. t_xrbindP.  move=> [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h0 y0 /of_val_int Hy' <- <- _.
  rewrite He in He'. rewrite Hy' in He'. rewrite Hy in He'.
  by case: He' => <- _.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y /of_val_int Hy h1 /of_val_int Hy' <- <- _.
  rewrite He He' /=. rewrite Hy Hy'. move=> [y6 y6'] Hh6 [y8 y8'] Hh8.
  move=> h10 h11 /of_val_int /= Hh10 h13 /of_val_int H13 <- <- _.
  rewrite Hh10 in Hh6. rewrite H13 in Hh8.
  case: Hh6 => <- _. by case: Hh8 => <- _.
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
  t_xrbindP. move=> h y /of_val_int Hy <- <- <-. rewrite Hy in He.
  rewrite He /=. exists (n1 - y)%Z.
  by split.
+ t_xrbindP. move=> [yv yl] He. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int /= Hy <- <- <-.
  case: eqP.
  - move=> Hn2. rewrite He. exists yv.
    split. auto. rewrite /=. rewrite Hn2. rewrite Hy. by rewrite Z.sub_0_r.
  move=> Hn2 /=. t_xrbindP. rewrite He /=. rewrite /sem_sop2 /=.
  rewrite Hy /=. exists (y - n2)%Z. by split.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y /of_val_int Hy h1 /of_val_int Hy' <- <- <-.
  rewrite He He' /=. rewrite Hy Hy' /=.
  exists (y - h1)%Z. by split.
Qed.

Lemma ssub_wP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Osub (Op_w sz)) e1 e2) = ok (v, l) ->
sem_pexpr gd s (ssub_w sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /ssub_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He' /=. move=> h4.
  rewrite /sem_sop2 /=. t_xrbindP. move=> y Hw h3 Hw' <- <- _ <- _.
  have := is_wconstP gd s h1; have := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2 Hw2. rewrite He /=. move=> h5 [] <- /=.
  rewrite Hw /=. move=> [] -> /=. rewrite He' in He2.
  case: He2 => He21 He22. rewrite He21 in Hw'.
  rewrite Hw' in Hw2. case: Hw2 => <-. by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move => h y Hyv h3 Hyv' <- <- _. rewrite He /=.
  rewrite He' /=. move=> h8 [] <- /= h10 [] <-. rewrite Hyv /=.
  rewrite Hyv' /=. by move=> b h13 [] <- h15 [] <- <- <- _.
+ case: eqP => // hz /=.
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have:= is_wconstP gd s h2.
    rewrite He' /=. move=> -> /=. move=> h y Hw' h3 [] <- <- <- /= Hl.
    rewrite He /=. apply of_val_word in Hw'. move: Hw'.
    move=> [] sz' [] x0 [] Hsz -> ->.
    rewrite hz /=. rewrite GRing.subr0. rewrite /word_uincl /zero_extend.
    move=> [] <- _ /=. rewrite Hsz. by rewrite andTb.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- _.
    rewrite He1 /=. move=> h8 [] <-. rewrite He2 /=. move=> h10 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite Hw /=. move=> h12 h13 [] <-. rewrite Hw' /=. by move=> h15 [] <- <- <- _.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- <- _. rewrite He1 /=. move=> [yv1 yl1] [] <- _.
  rewrite He2 /=. move=> [yv2 yl2] [] <- _. rewrite Hw Hw' /=. 
  by move=> h12 h13 [] <- h15 [] <- <- <- _.
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
  rewrite /sem_sop2 /=. t_xrbindP. move=> y Hw h3 Hw' <- <- Hl.
  have := is_wconstP gd s h1; have := is_wconstP gd s h2.
  t_xrbindP. move=> [yv2 yl2] He2. move=> Hw2. rewrite He /=.
  move=> h5 [] <-. rewrite Hw /=. move=> [] <- /=.
  rewrite He' in He2. case: He2 => He21 He22.
  rewrite He21 in Hw'. rewrite Hw2 in Hw'. case: Hw'=> [] ->.
  rewrite wrepr_unsigned. exists (Vword (y - h3)). by split.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move => h y Hyv h3 Hyv' <- <- <-. rewrite He /=.
  rewrite He' /=. rewrite Hyv Hyv' /=. exists (Vword (y - h3)).
  by split.
+ case: eqP => // hz /=. 
  - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
    rewrite /sem_sop2 /=. t_xrbindP. have:= is_wconstP gd s h2.
    rewrite He' /=. move=> -> /= h y Hw' h3 [] <- <- <- <-. rewrite He /=.
    apply of_val_word in Hw'. move: Hw'. move=> [] sz' [] x0 [] Hsz -> ->.
    rewrite hz /=. rewrite GRing.subr0. rewrite /word_uincl /zero_extend.
    exists (Vword x0). rewrite Hsz. by rewrite andTb.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hw h3 Hw' <- <- <-.
    rewrite He1 /=. rewrite He2 /=.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite Hw /=. rewrite Hw' /=. exists (Vword (y - h3)).
    by split.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hw h3 Hw' <- <- <-. rewrite He1 /=.
  rewrite He2 /=. rewrite Hw Hw' /=. exists (Vword (y - h3)).
  by split.
Qed.

Lemma ssubP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Osub ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (ssub ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
by case: ty; eauto using ssub_intP, ssub_wP.
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

Lemma smul_intP s e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Omul Op_int) e1 e2) = ok (v, l) ->
sem_pexpr gd s (smul_int e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /smul_int.
case: (is_constP e1) => [n1| {e1} e1];
case: (is_constP e2) => [n2| {e2} e2] /=.
+ by move=> [] <- _ [] <- _.
+ t_xrbindP. move=> [yv yl] He2. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hyv <- <- _.
  case:eqP => [-> //|_].
  - rewrite /=. by move=> [] <- _.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He2. rewrite He2.
    move=> [] <- _. by rewrite Z.mul_1_l.
  t_xrbindP. move=> [yv' yl'] He'.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h0 y0 /of_val_int Hyv'. rewrite Hyv' in He'.
  rewrite He' in He2. move=> <- <- _. rewrite Hyv in He2.
  by case: He2 => -> _.
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hyv <- <- _.
  case:eqP => [-> //|_].
  - rewrite /=. move=> [] <- _. by rewrite Z.mul_0_r.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He1. rewrite He1.
    move=> [] <- _. by rewrite Z.mul_1_r.
  t_xrbindP. move=> [yv' yl'] He'.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h0 y0 /of_val_int Hyv'. rewrite Hyv' in He'.
  rewrite He' in He1. move=> <- <- _. rewrite Hyv in He1.
  by case: He1 => -> _.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hyv h1 Hyv' <- <- _. rewrite He1 He2 /=.
  move=> [yv1 yv2] [] <- _ [yv3 yv4] [] <- _. rewrite Hyv Hyv' /=.
  by move=> h10 h11 [] <- h13 [] <- <- <- _.
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
  t_xrbindP. move=> h y /of_val_int Hyv <- <- <-.
  case:eqP => [-> //|_].
  - rewrite /=. exists 0%Z. by split.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He2. rewrite He2. exists y.
    split. auto. by rewrite Z.mul_1_l /=.
  t_xrbindP. rewrite He2 /=.
  rewrite /sem_sop2 /=. t_xrbindP. rewrite Hyv /=.
  exists (n1 * y)%Z. by split.
+ t_xrbindP. move=> [yv yl] He1. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y /of_val_int Hyv <- <- <-.
  case:eqP => [-> //|_].
  - rewrite /=. exists 0%Z. by rewrite Z.mul_0_r.
  case:eqP => [-> | _ /=].
  - rewrite Hyv in He1. rewrite He1.
    exists y. by rewrite Z.mul_1_r /=.
  t_xrbindP. rewrite He1 /=.
  rewrite /sem_sop2 /=. t_xrbindP. rewrite Hyv /=.
  exists (y * n2)%Z. by split.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  move=> h y Hyv h1 Hyv' <- <- <-. rewrite He1 He2 /=.
  rewrite Hyv Hyv' /=. exists (y*h1)%Z. by split.
Qed.

Lemma smul_wP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Omul (Op_w sz)) e1 e2) = ok (v, l) ->
sem_pexpr gd s (smul_w sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /smul_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  have:= is_wconstP gd s h1. have:= is_wconstP gd s h2.
  t_xrbindP. rewrite He2 /=. move=> u [] <- ->. rewrite He1 /=.
  move=> h3 [] <- -> h6 h7 [] <- h9 [] -> <- <- _ <- _.
  by rewrite wrepr_unsigned.
+ case: eqP => hn1.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have:= is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> [yv1 yl1] [] <- _ -> h3 h4 [] <- h6 Hyv' <- <- _ <- _.
    rewrite wrepr_unsigned hn1 /=. by rewrite GRing.mul0r.
  - case: eqP => hn2.
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- <- _.
      rewrite He' /=. move=> [] <- _. have:= is_wconstP gd s h1.
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He in He1'.
      case: He1' => <- He12. rewrite Hyv /=. move=> [] ->. rewrite hn2.
      rewrite GRing.mul1r. case: (of_val_word Hyv') => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      rewrite /word_uincl /zero_extend. by rewrite Hsz /=.
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- <- _. rewrite He2 /=.
    move=> [yv1 yl1] [] <- <-. rewrite /sem_sop2 /=. t_xrbindP.
    rewrite wrepr_unsigned truncate_word_u. move=> h0 y0 [] <- h5 Hv' <- <- _.
    rewrite Hyv' in Hv'. case: Hv' => ->. have:= is_wconstP gd s h1.
    rewrite He1 /=. rewrite Hyv /=. by move=> [] <-.
+ case: eqP => hn1.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> [yv1 yl1] [] <- <- -> h3 h4 Hyv h6 [] <- <- <- _ <- _.
    rewrite wrepr_unsigned hn1 /=. by rewrite GRing.mulr0.
  - case: eqP => hn2.
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- <- _.
      rewrite He /=. move=> [] <- _. have:= is_wconstP gd s h2.
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He' in He1'.
      case: He1'=> <- _. rewrite Hyv' /=. move=> [] ->. rewrite hn2.
      rewrite GRing.mulr1. case: (of_val_word Hyv) => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      rewrite /word_uincl /zero_extend. by rewrite Hsz /=.
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- <- _. rewrite He1 /=.
    move=> [yv1 yl1] [] <- _. rewrite /sem_sop2 /=. t_xrbindP.
    rewrite wrepr_unsigned truncate_word_u. move=> h0 y0 Hv' h5 [] <- <- <- _.
    rewrite Hyv in Hv'. case: Hv' => ->. have:= is_wconstP gd s h2.
    rewrite He2 /=. rewrite Hyv' /=.
    by move=> [] ->.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y Hyv h3 Hyv' <- <- _.
  rewrite He He' /=. move=> [yv1 yl1] [] <- _ [yv2 yl2] [] <- _.
  rewrite Hyv Hyv' /=. by move=> h12 h13 [] <- h15 [] <- <- <- _.
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
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  rewrite /sem_sop2 /=. t_xrbindP.
  have:= is_wconstP gd s h1. have:= is_wconstP gd s h2.
  t_xrbindP. rewrite He1 He2 /=. 
  move=> [yv1 yl1] [] <- _ -> [yv2 yl2] [] <- _ ->.
  move=> h6 h7 [] <- h9 [] <- <- <- _. rewrite wrepr_unsigned.
  exists (Vword (n1 * n2)). by split.
+ case: eqP => hn1.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have:= is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> [yv1 yl1] [] <- _ -> h3 h4 [] <- h6 Hyv' <- <- _.
    rewrite wrepr_unsigned hn1 /=. rewrite GRing.mul0r /=.
    eexists. split. auto. by rewrite /=.
  - case: eqP => hn2.
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- <- <-.
      rewrite He'. have:= is_wconstP gd s h1. 
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He in He1'.
      case: He1' => <- _. rewrite Hyv /=.
      move=> [] ->. rewrite hn2. rewrite GRing.mul1r.
      case: (of_val_word Hyv') => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      exists (Vword w). split. auto.
      rewrite /word_uincl /zero_extend. by rewrite Hsz /=.
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2 /=. rewrite /sem_sop2 /=.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- <- <-. rewrite He2 /=.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite wrepr_unsigned truncate_word_u. rewrite Hyv' /=.
    have:= is_wconstP gd s h1. t_xrbindP.
    move=> [yv1 yl1] He1'. rewrite He1 in He1'. case: He1' => <- _. rewrite Hyv /=.
    move=> [] -> /=. exists (Vword (n1 * h3)). by split.
+ case: eqP => hn1.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> [yv1 yl1] [] <- _ -> h3 h4 Hyv h6 [] <- <- <- _.
    rewrite wrepr_unsigned hn1 /=. rewrite GRing.mulr0.
    eexists. split. auto. by rewrite /=.
  - case: eqP => hn2.
    * t_xrbindP. move => [yv yl] He [yv' yl'] He'.
      rewrite /sem_sop2 /=. t_xrbindP. move=> h y Hyv h3 Hyv' <- <- <-.
      rewrite He /=. have:= is_wconstP gd s h2.
      t_xrbindP. move=> [yv1 yl1] He1'. rewrite He' in He1'. case: He1' => <- _.
      rewrite Hyv' /=. move=> [] ->. rewrite hn2. rewrite GRing.mulr1.
      case: (of_val_word Hyv) => {Hyv'} sz' [w] [Hsz ? ?]; subst.
      exists (Vword w). split. auto. rewrite /word_uincl /zero_extend.
      by rewrite Hsz /=.
    t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2. rewrite /sem_sop2 /=.
    t_xrbindP. move=> h y Hyv h3 Hyv' <- <- <-. rewrite He1 /=.
    rewrite /sem_sop2 /=. t_xrbindP.
    rewrite wrepr_unsigned truncate_word_u.
    rewrite Hyv. have:= is_wconstP gd s h2. rewrite He2 /=.
    rewrite Hyv' /=. move=> [] ->. exists (Vword (y * n2)). by split.
+ t_xrbindP. move=> [yv yl] He [yv' yl'] He'. rewrite /sem_sop2 /=.
  t_xrbindP. move=> h y Hyv h3 Hyv' <- <- <-.
  rewrite He He' /=. rewrite Hyv Hyv' /=.
  exists (Vword (y * h3)). by split.
Qed.

Lemma smulP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Omul ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (smul ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
by case: ty; eauto using smul_intP, smul_wP.
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

Lemma s_eqP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oeq ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (s_eq ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /s_eq; case:ifP => [ /eq_exprP Hs | _]; rewrite /=.
+ move: (Hs gd s). move=> Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'. rewrite Hs' in He.
  rewrite He in He'. case: He' => <- <-.
  rewrite /sem_sop2 ; case: ty => [ | sz ] /=.
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- <- _ <- _ /=.
    by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- <- _ <- _.
  by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _ [] <- _ /=. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- _. rewrite He /=.
     move=> h4 [] <-. rewrite Hyv /=.
     by move=> h6 h7 [] <- <- <- _.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- _. rewrite He1 /=.
     move=> h4 [] <-. rewrite Hyv /=.
     move=> h6 h7 [] <- <- <- _. auto.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- <- _. rewrite He He' /=.
     move=> h6 [] <- /= h8 [] <- /=. rewrite Hyv Hyv' /=.
     move=> h10 h11 [] <- h13 [] <- <- <- _. auto.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have:= is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> y0 [] <- /=. move => -> /= h3 h4 [] <-.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    by move=> y [] <- /= -> /= h5 [] <- <- <- _ <- _.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- <- _. rewrite He1 He2 /=.
    move=> h8 [] <- h10 [] <-. rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=. 
    by move=> h0 y0 [] <- h5 [] <- <- <- _.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- <- _. rewrite He1 He2 /=.
    move=> h7 [] <- h9 [] <-. rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
    by move=> h0 y0 [] <- h4 [] <- <- <- _.
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
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- <- _.
    exists true. by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- <- _.
  exists true. by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _. exists (n1 =? n2)%Z. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- <-. rewrite He /=.
     rewrite Hyv /=. by exists (n1 =? y)%Z.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- <-. rewrite He1 /=.
     rewrite Hyv /=. by exists (y =? n2)%Z.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- <- <-. rewrite He He' /=.
     rewrite Hyv Hyv' /=. by exists (y =? h1)%Z.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have:= is_wconstP gd s h1. t_xrbindP. rewrite He1 /=.
    move=> y0 [] <- /=. move => -> /= h3 h4 [] <-.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> y [] <- /= -> /= h5 [] <- <- <- _.
    by exists (n1 == n2)%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
    by exists (y == h3)%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
    by exists (y==h2)%Z.
Qed.

Lemma sneqP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oneq ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sneq ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sneq /s_eq; case:ifP => [ /eq_exprP Hs | _]; rewrite /=.
+ move: (Hs gd s). move=> Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'. rewrite Hs' in He. rewrite He in He'.
  case: He' => <- <- /=. rewrite /sem_sop2 ; case: ty => [ | sz ] /=.
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- <- _ <- _ /=.
    by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- <- _ <- _.
  by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _ [] <- _ /=. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- _. rewrite He /=.
     move=> h4 [] <-. rewrite Hyv /=.
     by move=> h6 h7 [] <- <- <- _.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- _. rewrite He1 /=.
     move=> h4 [] <-. rewrite Hyv /=.
     move=> h6 h7 [] <- <- <- _. auto.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- <- _. rewrite He He' /=.
     move=> h6 [] <- /= h8 [] <- /=. rewrite Hyv Hyv' /=.
     move=> h10 h11 [] <- h13 [] <- <- <- _. auto.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have:= is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> y0 [] <- /=. move => -> /= h3 h4 [] <-.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    by move=> y [] <- /= -> /= h5 [] <- <- <- _ <- _.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- <- _. rewrite He1 He2 /=.
    move=> h8 [] <- h10 [] <-. rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=. 
    by move=> h0 y0 [] <- h5 [] <- <- <- _.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- <- _. rewrite He1 He2 /=.
    move=> h7 [] <- h9 [] <-. rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
    by move=> h0 y0 [] <- h4 [] <- <- <- _.
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
  - t_xrbindP. move=> h y -> /= h1 [] -> /= <- <- _.
    exists false. by rewrite Z.eqb_refl.
  t_xrbindP. move=> h y -> /= h1 [] <- <- <- _.
  exists false. by rewrite eqxx.
case: ty.
 + case: (is_constP e1) => [n1| {e1} e1];
   case: (is_constP e2) => [n2| {e2} e2] //=.
   - move=> [] <- _. exists (~~ (n1 =? n2))%Z. auto.
   - t_xrbindP. move=> [yv yl] He.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- <-. rewrite He /=.
     rewrite Hyv /=. by exists (~~(n1 =? y))%Z.
   - t_xrbindP. move=> [yv yl] He1.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv <- <- <-. rewrite He1 /=.
     rewrite Hyv /=. by exists (~~(y =? n2))%Z.
   - t_xrbindP. move=> [yv yl] He [yv' yl'] He'.
     rewrite /sem_sop2 /=. t_xrbindP.
     move=> h y Hyv h1 Hyv' <- <- <-. rewrite He He' /=.
     rewrite Hyv Hyv' /=. by exists (~~(y =? h1))%Z.
+ move => sz. case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    have:= is_wconstP gd s h1. t_xrbindP.
    rewrite He1 /=. move=> y0 [] <- /=.
    move => -> /= h3 h4 [] <-.
    have:= is_wconstP gd s h2. t_xrbindP. rewrite He2 /=.
    move=> y [] <- /= -> /= h5 [] <- <- <- _.
    by exists (~~(n1 == n2))%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h3 Hyv' <- <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
    by exists (~~(y == h3))%Z.
  - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
    rewrite /sem_sop2 /=. t_xrbindP.
    move=> h y Hyv h2 Hyv' <- <- <-. rewrite He1 He2 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP. rewrite Hyv Hyv' /=.
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

Lemma sltP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Olt ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (slt ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /slt;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He => -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _ <- _. by rewrite Z.ltb_irrefl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _ <- _. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. by move=> [] <- _ [] <- _.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _ <- _ /=. by rewrite ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _ <- _. by rewrite ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
Qed.

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
  - t_xrbindP. move=> h y -> h1 [] -> <- <- _.
    exists false. by rewrite Z.ltb_irrefl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _. 
    exists false. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 <? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _. exists (wsigned w1 <? wsigned w2)%Z.
      by rewrite ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _. exists (wunsigned w1 <? wunsigned w2)%Z.
    by rewrite ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
Qed.

Lemma sleP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ole ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sle ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sle;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'. rewrite Hs' in He.
  rewrite He' in He. case: He => -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _ <- _.
    by rewrite Z.leb_refl.
  - t_xrbindP.
    move=> h y -> /= h1 [] <- <- <- _ <- _. by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. by move=> [] <- _ [] <- _.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _ <- _ /=. by rewrite ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _ <- _. by rewrite ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
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
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _.
    exists true. by rewrite Z.leb_refl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _. 
    exists true. by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 <=? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _. exists (wsigned w1 <=? wsigned w2)%Z.
      by rewrite ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _. exists (wunsigned w1 <=? wunsigned w2)%Z.
    by rewrite ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
Qed.

Lemma sgtP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ogt ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sgt ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sgt;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He.
  case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _ <- _.
    by rewrite Z.gtb_ltb Z.ltb_irrefl.
  - t_xrbindP.
    move=> h y -> /= h1 [] <- <- <- _ <- _. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. by move=> [] <- _ [] <- _.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _ <- _ /=. by rewrite Z.gtb_ltb ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _ <- _. by rewrite Z.gtb_ltb ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
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
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _.
    exists false. by rewrite Z.gtb_ltb Z.ltb_irrefl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _. 
    exists false. by rewrite wlt_irrefl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. exists (n1 >? n2)%Z.
    by split.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _. exists (wsigned w1 >? wsigned w2)%Z.
      by rewrite Z.gtb_ltb ssrZ.ltzE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _. exists (wunsigned w1 >? wunsigned w2)%Z.
    by rewrite Z.gtb_ltb ssrZ.ltzE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
Qed.

Lemma sgeP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oge ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sge ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /sge;case:ifP => [ /eq_exprP Hs /=| _ ].
+ move: (Hs gd s) => Hs'. t_xrbindP.
  move=> [yv yl] He [yv' yl'] He'.
  rewrite Hs' in He. rewrite He' in He. case: He=> -> -> /=.
  rewrite /sem_sop2; case: ty => [ | sg sz ] /=.
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _ <- _.
    by rewrite Z.geb_leb Z.leb_refl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _ <- _. 
    by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. by move=> [] <- _ [] <- _.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _ <- _ /=. by rewrite Z.geb_leb ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _ <- _. by rewrite Z.geb_leb ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- _ h7 [] <- h9 [] <-. rewrite Hs /=.
    by move=> h11 [] <- <- _.
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
  - t_xrbindP. move=> h y -> h1 [] <- <- <- _.
    exists true. by rewrite Z.geb_leb Z.leb_refl.
  - t_xrbindP. move=> h y -> /= h1 [] <- <- <- _. 
    exists true. by rewrite wle_refl.
+ is_cmp_const s. move=> n1 H. is_cmp_const s. move=> n2.
  case: ty H.
  - move=> -> -> /=. move=> [] <- _. by exists (n1 >=? n2)%Z.
  - move=> sg sz [] v1 [] l1 [] He1 [] w1 ok_v1 h1 [] v2 [] l2 [] He2 [] w2 ok_v2 /=.
    case: sg h1 => <- <-.
    * t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
      rewrite /sem_sop2 /=. rewrite ok_v1 ok_v2 /=.
      move=> h2 [] <- <- _. exists (wsigned w1 >=? wsigned w2)%Z.
      by rewrite Z.geb_leb ssrZ.lezE.
    t_xrbindP. rewrite He1 He2 /=. move=> y [] <- h0 [] <-.
    rewrite /sem_sop2 /=. t_xrbindP. rewrite ok_v1 ok_v2 /=.
    move=> h y0 [] <- h2 [] <- <- <- _. exists (wunsigned w1 >=? wunsigned w2)%Z.
    by rewrite Z.geb_leb ssrZ.lezE.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
  - move=> h /=. t_xrbindP. move=> y -> h1 -> /= h3 Hs.
    move=> <- <-. rewrite Hs /=. by exists h3.
Qed.

Lemma sbitwP i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 v' v'' s l l':
  (∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
  sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v ->
      v = Vword (z sz (zero_extend sz w1) (zero_extend sz w2))) ->
sem_pexpr gd s (Papp2 (i sz) e1 e2) = ok (v', l) ->
sem_pexpr gd s (sbitw i z sz e1 e2).1 = ok (v'', l') ->
value_uincl v' v''.
Proof.
rewrite /sbitw => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'. case: He1' => -> -> /=.
  case: He2' => -> -> /=. move=> Hyv Hyv' h5 Hs' <- _ <- _.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  rewrite Hw1 Hw2 in Hs'. move: (h sz1 w1 sz2 w2 h5 Hs'). 
  move=> -> /=. by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  move=> Hyv h4 Hs' <-_.
  rewrite He1 He2 /=. move=> h8 [] <- h10 [] <-. rewrite Hs' /=.
  by move=> h12 [] <- <- _.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- _.
move=> h8 [] <- h10 [] <-. rewrite Hs /=. by move => h12 [] <- <- _.
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
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He2 in He2'. case: He2'=> -> -> /=.
  move=> Hyv Hyv' h5 Hs' <- _.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  exists (Vword (wrepr sz (wunsigned (z sz (zero_extend sz w1) (zero_extend sz w2))))).
  split. auto. rewrite He1 in He1'. case: He1'=> He11 He12.
  rewrite He11 in Hs'. rewrite Hw1 in Hs'. rewrite Hw2 in Hs'.
  move: (h sz1 w1 sz2 w2 h5 Hs'). move=> -> /=. by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'. case: He1'=> <- <- /=.
  move=> Hyv h4 Hs' <- <-.
  rewrite He1 He2 /=. rewrite Hs' /=. exists h4. by split.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- <-.
rewrite Hs /=. by exists h4.
Qed.

Lemma slandP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oland ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sland ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
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

Lemma slorP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Olor ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (slor ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
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

Lemma slxorP s ty e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Olxor ty) e1 e2) = ok (v, l) ->
sem_pexpr gd s (slxor ty e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
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

Lemma sbitw8P i (z: ∀ sz, word sz → word U8 → word sz) sz e1 e2 v' v'' s l l':
  (∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
  sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v ->
      v = Vword (z sz (zero_extend sz w1) (zero_extend U8 w2))) ->
sem_pexpr gd s (Papp2 (i sz) e1 e2) = ok (v', l) ->
sem_pexpr gd s (sbitw8 i z sz e1 e2).1 = ok (v'', l') ->
value_uincl v' v''.
Proof.
rewrite /sbitw8 => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'.
  case: He1' => -> _. case: He2' => -> _. move=> Hyv Hyv' h5 Hs' <- _ <- _.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  rewrite Hw1 Hw2 in Hs'. move: (h sz1 w1 sz2 w2 h5 Hs'). 
  move=> -> /=. by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' <-_.
  rewrite He1 He2 /=. move=> h8 [] <- h10 [] <-. rewrite Hs' /=.
  by move=> h12 [] <- <- _.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- _.
move=> h8 [] <- h10 [] <-. rewrite Hs /=. by move => h12 [] <- <- _.
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
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'.
  case: He1' => -> _.
  case: He2' => -> _. move=> Hyv Hyv' h5 Hs' <- _.
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 ->.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 ->.
  rewrite Hw1 Hw2 in Hs'. move: (h sz1 w1 sz2 w2 h5 Hs'). 
  move=> -> /=. exists (Vword (wrepr sz (wunsigned (z sz (zero_extend sz w1) (zero_extend U8 w2))))).
  by rewrite wrepr_unsigned.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' <- <-.
  rewrite He1 He2 /=. rewrite Hs' /=. by exists h4. 
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- <-.
rewrite Hs /=. by exists h4.
Qed.

Lemma slslP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Olsl sz) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sshl sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitw8P => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
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

Lemma slsrP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Olsr sz) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sshr sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitw8P => sz1 w1 sz2 w2 v1.
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

Lemma sasrP s sz e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Oasr sz) e1 e2) = ok (v, l) ->
sem_pexpr gd s (ssar sz e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitw8P => sz1 w1 sz2 w2 v1.
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

Lemma sdivP s k e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Odiv k) e1 e2) = ok (v, l) ->
sem_pexpr gd s (sdiv k e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
case: k => [ | u sz] /=.
+ rewrite /soint.
  case: (is_constP e1) => [n1| {e1} e1];
  case: (is_constP e2) => [n2| {e2} e2] H H' /=;eauto.
  - move: H H'. rewrite /sem_sop2 /=. by move=> [] <- _ [] <- _.
  - move: H H'. t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] [] <- _.
    move=> [yv' yl'] -> /=. rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> /=.
    by move=> <- <- _ h4 h5 [] <- <- <- _.
  - move: H H'. t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] ->.
    move=> [yv' yl'] [] -> _ /=. rewrite /sem_sop2 /=. t_xrbindP.
    by move=> h y -> h1 -> /= <- <- _ h6 h7 [] -> h9 [] -> <- <- _.
  - move: H H'. t_xrbindP. rewrite /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
    by move=> h2 -> /= <- _ [] <- _.
    rewrite /sbituw.
    case h1: is_wconst => [ n1 | ] //.
    case h2: is_wconst => [ n2 | ] // /=.
    + case:eqP => // neq.
      - t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
        t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
        move=> h5 -> <- <- _. t_xrbindP. by move=> h9 y0 <- <- <- _.
      - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
      have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
      have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
      rewrite He1 in He1'. rewrite He2 in He2'.
      case: He1' => -> _. case: He2' => -> _.
      move=> Hyv Hyv' h4 Hs' <- _ /=.
      apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
      apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
      rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
      rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
      move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
      case: ifP => //. move=> H. move=> h5 [] <- <- <- _. rewrite -Hn /=.
      rewrite /zero_extend wrepr_unsigned. by case: u.
    + t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
      have := is_wconstP gd s h1. t_xrbindP.
      move=> [yv1 yl1] He1'. rewrite He1 in He1'.
      case: He1' => He11 He12. move=> Hyv h4 Hs' <-_.
      rewrite He1 He2 /=. move=> h8 [] <- h10 [] <-. rewrite Hs' /=.
      by move=> h12 [] <- <- _.
    rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- _.
    move=> h8 [] <- h10 [] <-. rewrite Hs /=. by move => h12 [] <- <- _.
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
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> h1 -> <- <- <- /=.
    by exists (y / h1)%Z.
rewrite /sbituw.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
- case:eqP => // neq.
  t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
  t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
  move=> h5 -> <- <- <-. t_xrbindP. rewrite /=. by exists (Vword h5).
  t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'. case: He1' => -> _.
  case: He2' => -> _. move=> Hyv Hyv' h4 Hs' <- _ /=. 
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
  rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
  rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
  move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
  case: ifP => //. move=> H.  move=> h5 [] <- <-.
  exists (Vword (wrepr sz (wunsigned (signed (@wdiv) (@wdivi) u sz n1 n2)))).
  rewrite -Hn /=. rewrite /zero_extend wrepr_unsigned. by case: u.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' <- <-.
  rewrite He1 He2 /=. rewrite Hs' /=. by exists h4.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- <-.
rewrite Hs /=. by exists h4.
Qed.

Lemma smodP s k e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Omod k) e1 e2) = ok (v, l) ->
sem_pexpr gd s (smod k e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
case: k => [ | u sz] /=.
+ rewrite /soint.
  case: (is_constP e1) => [n1| {e1} e1];
  case: (is_constP e2) => [n2| {e2} e2] H H' /=;eauto.
  - move: H H'. rewrite /sem_sop2 /=. by move=> [] <- _ [] <- _.
  - move: H H'. t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] [] <- _.
    move=> [yv' yl'] -> /=. rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> /=.
    by move=> <- <- _ h4 h5 [] <- <- <- _.
  - move: H H'. t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] ->.
    move=> [yv' yl'] [] -> _ /=. rewrite /sem_sop2 /=. t_xrbindP.
    by move=> h y -> h1 -> /= <- <- _ h6 h7 [] -> h9 [] -> <- <- _.
  - move: H H'. t_xrbindP. rewrite /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
    by move=> h2 -> /= <- _ [] <- _.
    rewrite /sbituw.
    case h1: is_wconst => [ n1 | ] //.
    case h2: is_wconst => [ n2 | ] // /=.
    + case:eqP => // neq.
      - t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
        t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
        move=> h5 -> <- <- _. t_xrbindP. by move=> h9 y0 <- <- <- _.
      - t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
      have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
      have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
      rewrite He1 in He1'. rewrite He2 in He2'.
      case: He1' => -> _. case: He2' => -> _. move=> Hyv Hyv' h4 Hs' <- _ /=. 
      apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
      apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
      rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
      rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
      move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
      case: ifP => //. move=> H. move=> h5 [] <- <- <- _. rewrite -Hn /=.
      rewrite /zero_extend wrepr_unsigned. by case: u.
    + t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
      have := is_wconstP gd s h1. t_xrbindP.
      move=> [yv1 yl1] He1'. rewrite He1 in He1'.
      case: He1' => He11 He12. move=> Hyv h4 Hs' <-_.
      rewrite He1 He2 /=. move=> h8 [] <- h10 [] <-. rewrite Hs' /=.
      by move=> h12 [] <- <- _.
    rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- _.
    move=> h8 [] <- h10 [] <-. rewrite Hs /=. by move => h12 [] <- <- _.
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
    rewrite /sem_sop2 /=. t_xrbindP. move=> h y -> h1 -> <- <- <- /=.
    by exists (y mod h1)%Z.
rewrite /sbituw.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] // /=.
- case:eqP => // neq.
  t_xrbindP. rewrite /sem_sop2 /=. move=> [yv yl] -> /= [yv' yl'] -> /=.
  t_xrbindP. rewrite /sem_sop2 /=. move=> h y -> h3 ->. rewrite /mk_sem_divmod /=.
  move=> h5 -> <- <- <-. t_xrbindP. rewrite /=. by exists (Vword h5).
  t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP. move=> [yv1 yl1] He1'.
  have := is_wconstP gd s h2. t_xrbindP. move=> [yv2 yl2] He2'.
  rewrite He1 in He1'. rewrite He2 in He2'.
  case: He1' => -> _. case: He2' => -> _. move=> Hyv Hyv' h4 Hs' <- _ /=. 
  apply of_val_word in Hyv'. move: Hyv'. move=> [] sz1 [] w1 [] Hsz1 /= Hw1 Hn.
  apply of_val_word in Hyv. move: Hyv. move=> [] sz2 [] w2 [] Hsz2 /= Hw2 Hn2.
  rewrite Hw1 Hw2 in Hs'. rewrite /=. move: Hs'. rewrite /sem_sop2 /=.
  rewrite /truncate_word Hsz1. rewrite /truncate_word Hsz2. t_xrbindP.
  move=> y <- h0 <-. rewrite /mk_sem_divmod. rewrite -Hn2 /=.
  case: ifP => //. move=> H.  move=> h5 [] <- <-.
  exists (Vword (wrepr sz (wunsigned (signed (@wmod) (@wmodi) u sz n1 n2)))).
  rewrite -Hn /=. rewrite /zero_extend wrepr_unsigned. by case: u.
+ t_xrbindP. move=> [yv yl] He1 [yv' yl'] He2.
  have := is_wconstP gd s h1. t_xrbindP.
  move=> [yv1 yl1] He1'. rewrite He1 in He1'.
  case: He1' => He11 He12. move=> Hyv h4 Hs' <- <-.
  rewrite He1 He2 /=. rewrite Hs' /=. by exists h4.
rewrite /=. t_xrbindP. move=> y -> /= h2 -> /= h4 Hs <- <-.
rewrite Hs /=. by exists h4.
Qed.

Lemma svaddP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovadd ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svadd ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
apply: rbindP => v2 /truncate_wordP [_ ->].
apply: rbindP => v3 /truncate_wordP [_ ->].
by case.
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

Lemma svsubP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovsub ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svsub ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
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

Lemma svmulP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovmul ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svmul ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: sbitwP => sz1 w1 sz2 w2 v1.
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

Lemma svshlP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovlsl ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svshl ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: @sbitw8P => sz1 w1 sz2 w2 v1.
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

Lemma svshrP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovlsr ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svshr ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: @sbitw8P => sz1 w1 sz2 w2 v1.
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

Lemma svsarP s ve ws e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 (Ovasr ve ws) e1 e2) = ok (v, l) ->
sem_pexpr gd s (svsar ve ws e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
apply: @sbitw8P => sz1 w1 sz2 w2 v1.
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

Lemma s_op2P s o e1 e2 v v' l l': 
sem_pexpr gd s (Papp2 o e1 e2) = ok (v, l) ->
sem_pexpr gd s (s_op2 o e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
  case: o;eauto using sandP, sorP, saddP, smulP, ssubP, sdivP, smodP,
                      s_eqP, sneqP, sltP, sleP, sgtP, sgeP,
                      slandP, slorP, slxorP, slslP, slsrP, sasrP,
                      svaddP, svsubP, svmulP, svshlP, svshrP, svsarP.
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

(* vuincl_sopn
Lemma app_sopn_uincl_a T ts op vs vs' (vres: T) :
  all is_not_sarr ts ->
  app_sopn ts op vs = ok vres ->
  List.Forall2 value_uincl_a vs vs' ->
  app_sopn ts op vs' = ok vres.
Proof.
  elim: ts op vs vs' => /=.
  + by move=> ? [] //= [] //= ???? /List_Forall2_inv_l.
  move=> t ts hrec op [] //= v vs vs'' /andP [ ht hts];t_xrbindP => w hw hop.
  case/List_Forall2_inv_l => v' [vs'] [->] {vs''} [hv hvs].
  rewrite (of_val_uincl_a hv hw) /=.
  by apply: hrec hvs.
Qed.
*)

(* vuincl_sem_opN
Lemma sem_opN_uincl_a op vs v vs' :
  sem_opN op vs = ok v →
  List.Forall2 value_uincl_a vs vs' →
  ∃ v' : value, sem_opN op vs' = ok v' ∧ value_uincl_a v v'.
Proof.
  rewrite /sem_opN; apply: rbindP => w ok_v' [<-{v}] h.
  rewrite (app_sopn_uincl_a _ ok_v' h) /=; first by eauto.
  by case: op {w ok_v'} => //= sz p; rewrite all_nseq orbT.
Qed.
*)

Lemma s_opNP op s es v v' l l':
 sem_pexpr gd s (PappN op es) = ok (v, l) ->
 sem_pexpr gd s (s_opN op es).1 = ok (v', l') ->
 value_uincl v v'.
Proof.
rewrite /s_opN.
case hi: (mapM _ _) => [ i | ] //=. 
case heq: (sem_opN _ _) => [ v1 | ] //.
case: v1 heq => // sz w'. case: (op) => sz' pe /=.
- rewrite /sem_opN. t_xrbindP.
  move=> y Hm y' h Ha <- <- _. rewrite Hm.
  move=> h6 [] <-. rewrite Ha /=.
  by move=> h8 h9 [] <- <- <- _.
+ rewrite /sem_opN /=. t_xrbindP.
  move=> y -> /= h0 h1 Ha <- <- _ h6 [] <-.
  rewrite /sem_opN /=. t_xrbindP.
  move=> h y0 Ha' <- <- _. rewrite Ha in Ha'.
  by case: Ha' => ->.
+ rewrite /sem_opN /=. t_xrbindP.
  move=> y Ha Hv h1 -> h3 h4 Ha' <- <- _ h9 [] <-.
  rewrite /sem_opN /=. t_xrbindP. rewrite Ha' /=.
  by move=> h y0 [] <- <- <- _.
+ rewrite /sem_opN /=; t_xrbindP. 
  move=> y Ha Hv. move=> h1 Hm. rewrite wrepr_unsigned.
  move=> h3 h4 /= Ha' /=. move=> <- <- _ <- _ /=. rewrite -Hv /=.
  admit.
+ rewrite /sem_opN /=. t_xrbindP.
  move=> y -> h0 h1 Ha <- <- _ h6 [] <-.
  rewrite /sem_opN /=. t_xrbindP.
  rewrite Ha /=. by move=> h y0 [] <- <- <- _.
+ rewrite /sem_opN /=. t_xrbindP.
  move=> y -> /= h0 h1 Ha <- <- _ h6 [] <-.
  rewrite /sem_opN /=. t_xrbindP.
  rewrite Ha /=. by move=> h y0 [] <- <- <- _.
+ t_xrbindP. move=> y -> /=. rewrite /sem_opN /=.
  t_xrbindP. move=> h y0 Ha <- <- _ h4 <-.
  rewrite Ha /=. by move=> h6 h7 [] <- <- <- _.
Admitted.

Lemma s_opNPl s op es v l:
let e' := (s_opN op es).1 in
let t := (s_opN op es).2 in
sem_pexpr gd s (PappN op es)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
Admitted.

Lemma s_ifP s t e e1 e2 v v' l l':
sem_pexpr gd s (Pif t e e1 e2) = ok (v, l) ->
sem_pexpr gd s (s_if t e e1 e2).1 = ok (v', l') ->
value_uincl v v'.
Proof.
rewrite /s_if /=. t_xrbindP.
move=> [yv yl] He h0 Hb. case: is_boolP He.
move=> a. case: a.
- move=> He [yv1 yl1] He1 [yv2 yl2] He2.
  move=> h6 Ht h8 Ht' <- Hl. rewrite He1 /=.
  move=> [] <- Hl1. rewrite /sem_pexpr in He.
  case: He => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. case: Hb => <-.
  by move : (value_uincl_truncate_val Ht).
- move=> He [yv1 yl1] He1 [yv2 yl2] He2.
  move=> h6 Ht h8 Ht' <- Hl. rewrite He2 /=.
  move=> [] <- Hl1. rewrite /sem_pexpr in He.
  case: He => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. case: Hb => <-.
  by move : (value_uincl_truncate_val Ht').
- move=> e0 He0 [yv1 yl1] He1 [yv2 yl2] He2 h6 Ht h8 Ht' <- Hl /=.
  rewrite He0 /=. rewrite Hb /=. rewrite He1 /=.
  rewrite He2 /=. rewrite Ht /=. rewrite Ht' /=.
  by move=> [] -> _.
Qed.

Lemma s_ifPl s ty e e1 e2 v l:
let e' := (s_if ty e e1 e2).1 in
let t := (s_if ty e e1 e2).2 in
sem_pexpr gd s (Pif ty e e1 e2)  = ok (v, l) ->
exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
value_uincl (trans_sem t (v, l)).1 v'.
Proof.
rewrite /s_if /=. rewrite /trans_sem. t_xrbindP.
move=> [yv yl] He h0 Hb. case: is_boolP He.
move=> a. case: a.
- move=> He [yv1 yl1] He1 [yv2 yl2] He2.
  move=> h6 Ht h8 Ht' <- <- /=.
  exists yv1. split. auto.
  rewrite /sem_pexpr in He.
  case: He => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. case: Hb => <-.
  by move : (value_uincl_truncate_val Ht). auto.
- move=> He [yv1 yl1] He1 [yv2 yl2] He2.
  move=> h6 Ht h8 Ht' <- Hl. rewrite He2 /=.
  rewrite /= in Hl. rewrite -Hl.
  exists yv2. split. auto.
  rewrite /sem_pexpr in He.
  case: He => He1' He2'. rewrite -He1' in Hb.
  rewrite /= in Hb. case: Hb => <-.
  by move : (value_uincl_truncate_val Ht').
- move=> e0 He0 [yv1 yl1] He1 [yv2 yl2] He2 h6 Ht h8 Ht' <- <- /=.
  rewrite He0 /=. rewrite Hb /=. rewrite He1 /=.
  rewrite He2 /=. rewrite Ht /=. rewrite Ht' /=.
  by exists (if h0 then h6 else h8).
Qed.

Definition vconst c :=
  match c with
  | Cint z => Vint z
  | Cword sz z => Vword z
  end.

Definition valid_cpm (vm: vmap)  (m:cpm) :=
  forall x n, Mvar.get m x = Some n -> get_var vm x = ok (vconst n).

Section CONST_PROP.
Context s m (Hvalid: valid_cpm (evm s) m).
Lemma compile_lp e v l:
 let e' := (const_prop_e m e).1 in
 let t := (const_prop_e m e).2 in
 sem_pexpr gd s e = ok (v, l) ->
 exists v', sem_pexpr gd s e' = ok (v', (trans_sem t (v, l)).2) /\
 value_uincl (trans_sem t (v, l)).1 v'.
Proof.
elim: e v l => //=; rewrite /trans_sem.
+ move=> z v l [] <- <- /=. by exists z.
+ move=> b v l [] <- <- /=. by exists b.
+ move=> n v l [] <- <- /=. by exists (Varr (WArray.empty n)).
+ move=> x v l. move: Hvalid => /(_ x).
  case: Mvar.get => [n /(_ _ erefl) | _ /= -> ]; last by eauto.
  move=> -> /= [] <- Hl.
  case: n => [ n | sz w ] /=. by exists n.
  exists (Vword (wrepr sz (wunsigned w))). split.
  auto. by rewrite wrepr_unsigned.
+ t_xrbindP. rewrite /=. move=> h h0 hl y -> <- <- /=.
  by exists y.
+ move=> sz x e He. move=> v l.
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
  t_xrbindP. move=> [yv yl] He' /=. move: (He yv yl He').
  move=> [] xv [] He'' /= Hv. move=> h0 Hyv h2 Hw <- <-.
  rewrite Hg /=. rewrite He'' /=.
  move: (value_uincl_int Hv Hyv). move=> [] Hyv' ->.
  rewrite Hyv' in Hyv. rewrite Hyv /=. rewrite Hw /=.
  exists (Vword h2). split. auto. auto.
+ move=> sz x e He. move=> v l.
  t_xrbindP. move=> y h Hg Hp [yv yl] He' h4 Hp' h6 Hr <- <-.
  move: (He yv yl He'). move=> [] xv [] He'' /= Hl.
  exists (Vword h6).
  rewrite Hg /=. rewrite Hp /=. rewrite He'' /=.
  move: (value_uincl_word Hl Hp'). move=> -> /=.
  rewrite Hr /=. by split.
+ move=> op e He. move=> v l. t_xrbindP.
  move=> [yv yl] /He [] x [] He' Hyv h0 Hop <- <-.
  apply /s_op1Pl. rewrite /=. rewrite He' /=.
  move: (vuincl_sem_sop1 Hyv Hop). by move=> -> /=.
+ move=> op e1 He1 e2 He2 v l. t_xrbindP.
  move=> [yv yl] /He1 [] x [] He1' Hyv.
  move=> [yv1 yl'] /He2 [] x1 [] He2' Hyv'.
  move=> h2 Ho <- <-.
  apply /s_op2Pl. rewrite /=. rewrite He1' /=.
  rewrite He2' /=. move: (vuincl_sem_sop2 Hyv Hyv' Ho).
  by move=> -> /=.
+ move=> op es ih v l. t_xrbindP.
  move=> vs Hm h0 Ho <- <- /=. apply s_opNPl.
  rewrite /=. rewrite Hm /=. by rewrite Ho /=.
+ move=> t e He e1 He1 e2 He2 v l. t_xrbindP.
  move=> [yv yl] /He/= [] x [] He' Hyv h0 
  /(value_uincl_bool Hyv) [] Hx Hxl; subst.
  move=> [yv1 yl1] /He1/= [] x1 [] He1' Hyv1.
  move=> [yv2 yl2] /He2/= [] x3 [] He2' Hyv2.
  move=> h6 /(truncate_value_uincl Hyv1) [] x Ht Hv h8
  /(truncate_value_uincl Hyv2) [] x0 Ht' Hv'.
  move=> <- <-.
  rewrite /s_if. case: is_boolP He'.
  - move=> a. case: (a).
    * move=> /= Htr. case: Htr => <- Hlt. exists x1.
      rewrite He1' /=. split. auto. move : (value_uincl_truncate_val Ht).
      move=> Ht1. by move : (value_uincl_trans Hv Ht1).
    move=> /= Htr. case: Htr => <- Hlt. exists x3.
    split. auto. move : (value_uincl_truncate_val Ht').
    move=> Ht1. by move : (value_uincl_trans Hv' Ht1).
  rewrite /=. move=> h -> /=. rewrite He1' /=.
  rewrite He2' /=. rewrite Ht Ht' /=.
  exists (if h0 then x else x0). split.
  auto. by case: (h0).
Qed.

End CONST_PROP.

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
                    LSub (unzip2 vs') = leak_F (LT_seq t) (LSub (unzip2 vs)).
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
  exists (((x, leak_F (const_prop_e m e).2 yl1) :: x0)).
  split. auto. split. apply List.Forall2_cons. auto. auto.
  case: Hl' => <-. auto.
- move=> z v l [] <- <-. by exists z.
- move=> b v l [] <- <-. by exists b.
- move=> n v l [] <- <-. by exists (Varr (WArray.empty n)).
- move=> x v l. move: Hvalid => /(_ x).
  case: Mvar.get => [n /(_ _ erefl) | _ /= -> ]; last by eauto.
  move=> -> /= [] <- Hl.
  case: n => [ n | sz w ] /=. exists n.
  by split. exists (Vword (wrepr sz (wunsigned w))). split.
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
  move=> [yv yl] /He [] x [] He' Hyv h0 Hop <- <-.
  apply /s_op1Pl. rewrite /=. rewrite He' /=.
  move: (vuincl_sem_sop1 Hyv Hop). by move=> -> /=.
+ move=> op e1 He1 e2 He2 v l. t_xrbindP.
  move=> [yv yl] /He1 [] x [] He1' Hyv.
  move=> [yv1 yl'] /He2 [] x1 [] He2' Hyv'.
  move=> h2 Ho <- <-.
  apply /s_op2Pl. rewrite /=. rewrite He1' /=.
  rewrite He2' /=. move: (vuincl_sem_sop2 Hyv Hyv' Ho).
  by move=> -> /=.
+ move=> op es ih v l. t_xrbindP.
  move=> vs Hm h0 Ho <- <- /=. apply s_opNPl.
  rewrite /=. rewrite Hm /=. by rewrite Ho /=.
+ move=> t e He e1 He1 e2 He2 v l. t_xrbindP.
  move=> [yv yl] /He/= [] x [] He' Hyv h0 
  /(value_uincl_bool Hyv) [] Hx Hxl; subst.
  move=> [yv1 yl1] /He1/= [] x1 [] He1' Hyv1.
  move=> [yv2 yl2] /He2/= [] x3 [] He2' Hyv2.
  move=> h6 /(truncate_value_uincl Hyv1) [] x Ht Hv h8
  /(truncate_value_uincl Hyv2) [] x0 Ht' Hv'.
  move=> <- <-.
  rewrite /s_if. case: is_boolP He'.
  - move=> a. case: (a).
    * move=> /= Htr. case: Htr => <- Hlt. exists x1.
      rewrite He1' /=. split. auto. move : (value_uincl_truncate_val Ht).
      move=> Ht1. by move : (value_uincl_trans Hv Ht1).
    move=> /= Htr. case: Htr => <- Hlt. exists x3.
    split. auto. move : (value_uincl_truncate_val Ht').
    move=> Ht1. by move : (value_uincl_trans Hv' Ht1).
  rewrite /=. move=> h -> /=. rewrite He1' /=.
  rewrite He2' /=. rewrite Ht Ht' /=.
  exists (if h0 then x else x0). split.
  auto. by case: (h0).
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
  case: e He => // [ n | [] // sz [] //= q ] [<-].
  + case: v => //= ?;last first.
    + by rewrite compat_typeC => /eqP ->; case: ty.
    move=> -> /truncate_val_int [_ ->].
    case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
    have := Hv z n0.
    case: ({| vtype := sint; vname := xn |} =P z).
    + move=> <- /=;rewrite Mvar.setP_eq=> ? -[] <-;by rewrite /get_var Fv.setP_eq.
    by move=> /eqP Hneq;rewrite Mvar.setP_neq.
  case: v => //= s ;last first.
  + by rewrite compat_typeC; case: s => //= s' _;case: ty.
  move=> w /andP[] Ule /eqP -> /truncate_val_word [] szw [] -> hle -> /=.
  rewrite !(zero_extend_wrepr _ Ule, zero_extend_wrepr _ (cmp_le_trans hle Ule), zero_extend_wrepr _ hle).
  case: x => -[] [] //= szx xn vi /=. t_xrbindP => ve vm.
  (*apply: set_varP => //= w' [<-] <- [<-] /= Hv z /= n.
  have := Hv z n.
  case: ({| vtype := sword szx; vname := xn |} =P z).
  + move=> <- /=. rewrite Mvar.setP_eq=> ? -[] <-; rewrite /get_var Fv.setP_eq /=.
    by f_equal; case: Sumbool.sumbool_of_bool => h;rewrite h.
  by move=> /eqP Hneq;rewrite Mvar.setP_neq.*)
 Admitted.

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

Check const_prop_rvs.

Check write_lvals.

Lemma const_prop_rvsP s1 s2 m x v:
  let c' := ((const_prop_rvs m x).1).1 in
  let e' := ((const_prop_rvs m x).1).2 in
  let t' := ((const_prop_rvs m x).2) in 
  valid_cpm (evm s1) m ->
  write_lvals gd s1 x v = Ok error s2 ->
  valid_cpm (evm s2.1) c' /\
  write_lvals gd s1 e' v = ok (s2.1, [:: leak_F (LT_seq t') (LSub s2.2)]).
Proof.
  elim: x v m s1 s2 => [ | x xs Hrec] [ | v vs] //= m s1 [s2 l2] Hm.
  + move=> [] /=. move=> <- _. split. auto. rewrite /write_lvals /=.
    admit.
  apply: rbindP. t_xrbindP. move=> [hs hl] [yv yl] Hw /= [] <- <- Hws.
  case hrv: const_prop_rv => [m1 l1].
  case: m1 hrv => mi vi hrv. case hrvs: const_prop_rvs => [ms ls].
  case: ms hrvs=> msi vis hrvs. move: const_prop_rvP. move=> Hrv.
  move: (Hrv s1 (yv, yl) m 

write_lval gd x v (s1, [::]).1 =
     ok (yv, yl)
  
  Admitted.
(*Lemma const_prop_rvsP s1 s2 m x v:
  let et := map (const_prop_rv m
  valid_cpm (evm s1) m ->
  write_lvals_e gd s1 x v = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rvs m x).1 /\
  write_lvals gd s1 (const_prop_rvs m x).2 v = ok s2.
Proof.
  elim: x v m s1 s2 => [ | x xs Hrec] [ | v vs] //= m s1 s2 Hm.
  + by move=> [<-].
  apply: rbindP => s1' Hw Hws.
  have [/=]:= const_prop_rvP Hm Hw.
  case Hx : const_prop_rv => [m1 rv'] /= Hm1 Hw'.
  have [/=]:= Hrec _ _ _ _ Hm1 Hws.
  by case Hxs : const_prop_rvs => [m2 rvs'] /= ?;rewrite Hw'.
Qed.*)


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
  write_lval_e gd x v s1 = ok (s2, lw) ->
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
  write_lval_e gd x v s = ok (s', lw) ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv.
       apply: (valid_cpm_rm _ Hv).
       apply vrvP_e with v lw. auto.
Qed.

End GLOB_DEFS.

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
  + move=> t e He e1 He1 e2 He2.
    by rewrite He He1 He2.
Qed.

Check const_prop_rv.

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
  by case: e => //= [n | [] // sz [] // n ]; rewrite Hm.
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
  case: Mvar.get (remove_cpm_spec m1 s1 z) => [? |];
   case: Mvar.get (remove_cpm_spec m2 s2 z) => [? |] => //.
  + by rewrite Hm => -[] -> _ [[]] ->.
  + by rewrite Hm Hs => -[ -> | ? ] [].
  by rewrite Hm Hs => -[] -> ? [] .
Qed.

Definition Mvarc_eq T := RelationPairs.RelProd (@Mvar_eq T) (@eq cmd).

Definition Mvarcl_eq T := RelationPairs.RelProd (RelationPairs.RelProd (@Mvar_eq T) (@eq cmd)) (@eq leak_i_tr).

Definition Mvarcls_eq T := RelationPairs.RelProd (RelationPairs.RelProd (@Mvar_eq T) (@eq cmd)) (@eq (seq leak_i_tr)).

Section PROPER.

  (*Let Pr (i:instr_r) :=
    forall ii m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_ir m1 ii i) (const_prop_ir m2 ii i).*)
  Let Pr (i:instr_r) := forall ii m1 m2, Mvar_eq m1 m2 -> Mvarcl_eq (const_prop_ir m1 ii i) (const_prop_ir m2 ii i).
                                                                          
  (*Let Pi (i:instr) :=
    forall m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_i m1 i) (const_prop_i m2 i).*)

  Let Pi (i:instr) :=
    forall m1 m2, Mvar_eq m1 m2 -> Mvarcl_eq (const_prop_i m1 i) (const_prop_i m2 i).

  (*Let Pc (c:cmd) :=
    forall m1 m2, Mvar_eq m1 m2 ->
    Mvarc_eq (const_prop const_prop_i m1 c) (const_prop const_prop_i m2 c).*)

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
    rewrite /Mvarcl_eq /=. rewrite /RelationPairs.RelProd /RelationPairs.RelCompFun /=.
    split; rewrite /=. split; rewrite /=. auto. rewrite /=.
    do 3 f_equal.
    Admitted.
    (*move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.*)

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
    + move: (Hc1 m1 m2 Heq). case: const_prop; move=> [m1' c1'] l1';
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
    do 3 f_equal.
    Admitted.
    (*move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.*)

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
  Notation gd := (p_globs p).

  Hypothesis (p'_def : p' = (const_prop_prog p).1).

  Let Pi s1 i li s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) ((const_prop_i m i).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem_c_i p' {|emem := emem s1; evm := vm1|} ((const_prop_i m i).1).2 (leak_I li (const_prop_i m i).2)
                         {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  Let Pi_r s1 i li s2 :=
    forall m ii,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) ((const_prop_ir m ii i).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem_c_i p' {|emem := emem s1; evm := vm1|} ((const_prop_ir m ii i).1).2 (leak_I li (const_prop_ir m ii i).2)
                         {|emem := emem s2; evm := vm2|} /\ 
          vm_uincl (evm s2) vm2.

  Let Pc s1 c lc s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) ((const_prop const_prop_i m c).1).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem_c_i p' {|emem := emem s1; evm := vm1|} ((const_prop const_prop_i m c).1).2 
                         (leak_Is leak_I (const_prop const_prop_i m c).2 lc)
                         {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  Let Pfor (i:var_i) zs s1 c lf s2 :=
    forall m,
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s1.(evm) m ->
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem_for_i p' i zs {|emem := emem s1; evm := vm1|} ((const_prop const_prop_i m c).1).2 
                                (leak_Iss leak_I (const_prop const_prop_i m c).2 lf)
                                {|emem := emem s2; evm := vm2|} /\
          vm_uincl (evm s2) vm2.

  (* Maybe fix this *)
  Let Pfun m1 fd vargs lf m2 vres :=
    forall vargs',
      List.Forall2 value_uincl vargs vargs' ->
      exists vres',
        sem_call_i p' m1 fd vargs' lf m2 vres' /\
        List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil_i Pc.
  Proof.
    by move=> s m /= ?;split=>// vm1 hu1;exists vm1;split => //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons_i p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hi Hpi Hc Hci m /= hvm.
    case heqi : const_prop_i => [mc lti]; case: mc heqi => mi ci heqi. 
    case heqc : const_prop => [mc ltc]; case: mc heqc => mc cc heqc.
    split. rewrite /=. rewrite /Pc in Hci. rewrite /Pi in Hpi.
    move: (Hpi m hvm). rewrite heqi /=. move=> [] hvm2 Hpi'.
    move: (Hci mi hvm2). rewrite heqc /=. by move=> [] hvm3 Hci'.
    move=>vmi Hm. rewrite /Pi in Hpi. rewrite /Pc in Hci.
    move: (Hpi m hvm). rewrite heqi /=. move=> [] hvm' H.
    move: (H vmi Hm). move=> [] vm2 [] Hci' Hvm'.
    move: (Hci mi hvm'). rewrite heqc /=. move=> [] hvm3 H'.
    move: (H' vm2 Hvm'). move=> [] vm3 [] Hci'' Hvm''.
    exists vm3. split => //.
    by apply sem_app_i with  {| emem := emem s2; evm := vm2 |}.
  Qed.
    
  Local Lemma HmkI : sem_Ind_mkI_i p Pi_r Pi.
  Proof.
    move=> ii i s1 s2 li Hi Hpi.
    rewrite /Pi_r in Hpi. rewrite /Pi. move=> m H.
    move: (Hpi m ii H). move=> [] H' Hvm. split=> //.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn_i p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' le lw He Ht Hw m ii Hm.
    move: (const_prop_eP). move=> Hcp.
    move: (Hcp gd e s1 m Hm v le He). move=> [] v'0 [] l' [] He' [] Hv Hl.
    move: (const_prop_rvP). move=> Hwp.
    move: (Hwp gd s1 (s2, lw) m x v'). case heqv: const_prop_rv => [m' c'].
    case: m' heqv=> mi ci heqv. rewrite /=. move=> H1.
    move: (H1 Hm Hw). move=> [] s2' [] l2' [] Hm' [] Hw' [] Hwv Hwl.
    case heqe: const_prop_e => [me l]. rewrite heqv /=; split. rewrite /= in Hv. 
    + move: add_cpmP. move=> Ha. rewrite Hwv in Hm'.
      move: (Ha gd s1 (s2', l2') mi ci (const_prop_e m e).1 tag ty (v'0, l') v v'
                He' Hv Ht Hw' Hm'). rewrite heqe /=. rewrite Hwv. move=> H. auto.
    move=> vm1 Hm1. move: (sem_pexpr_uincl). move: (const_prop_e_sem_pexprs_e')
    Admitted.
   (*have [v1 [H U]] := const_prop_eP Hm He.
    have [] := const_prop_rvP Hm Hw.
    case: const_prop_rv. move=> [m' cm'] x' /= Hm' Hw';split.
    + move: add_cpmP. move=> Ha.
      move: (Ha gd s1 (s2, lw) ).
    move=> s1 s2 x tag ty e v v' He htr Hw m ii /= Hm.
    have [v1 [H U]] := const_prop_eP Hm He.
    have [] := const_prop_rvP Hm Hw.
    case: const_prop_rv => m' x' /= Hm' Hw';split.
    + by eapply add_cpmP;eauto.
    move=> vm1 hvm1.
    have [v1' hv1' uv1']:= sem_pexpr_uincl hvm1 H.
    have [v2 htr2 hv']:= truncate_value_uincl U htr.
    have [v3 htr3 hv3]:= truncate_value_uincl uv1' htr2.
    have [vm2 hw hvm2]:= write_uincl hvm1 (value_uincl_trans hv' hv3) Hw'.
    exists vm2;split => //.
    apply sem_seq1;constructor;econstructor;eauto.
  Qed.*)

  Local Lemma Hopn : sem_Ind_opn_i p Pi_r.
  Proof.
    move=> s1 s2 t o xs es lo H m ii Hm; apply : rbindP H. move=> [vs ls].
    t_xrbindP=> Hes ves Hex [s le] Hw He Hl.
    move:(const_prop_esP'). move=> Hes'. move: (Hes' gd es s1 m Hm vs ls Hes).
    move=> [] v' [] l' [] Hess [] Hvv Hll.
    move:(const_prop_rvsP). move=> Hw'. move: (Hw' gd s1 (s, le) m xs ves).
    move=> Hw''. move: (Hw'' Hm Hw).
    move=> [] s2' [] l2' [] Hmw [] Hws [] Hse Hlw /=.
    case  hrvs: const_prop_rvs => [m' lt']. case: m' hrvs=> m' c' hrvs /=; split => //.   rewrite hrvs in Hmw. rewrite /= in Hmw. rewrite /= in He. rewrite -He. auto.
    move=> vm1 hvm1. move: write_lvals_cp. move=> H.
    move: (H gd s1 (const_prop_rvs m xs).1.2 ves s2' l2' Hws). move=> Hws'.
    move: (writes_uincl). move=> H'.
    move: (H' gd s1 s2' vm1 (const_prop_rvs m xs).1.2 ves _ (lest_to_les l2') hvm1
              (List_Forall2_refl _ value_uincl_refl) Hws'). move=> [] x Hws'' Hvm'.
    move: (write_lval_es_cp). move=> Hws3.
    move: (Hws3 gd  {| emem := emem s1; evm := vm1 |} (const_prop_rvs m xs).1.2 ves
                {| emem := emem s2'; evm := x |} (lest_to_les l2') Hws'').
    move=> [] l'0 [] Hlee Hwe.
    exists x. rewrite /=; split => //. apply sem_seq1_i. rewrite -Hl /=.
    apply EmkI_i. apply Eopn_i. rewrite /=. rewrite /sem_sopn_e.
    move: (const_prop_e_esP_sem_pexprs_e'). move=> Hess'.
    move: (Hess' gd s1 (unzip1 [seq const_prop_e m i | i <- es]) (v', l') Hess).
    move=> /= Hess''. move: sem_pexprs_uincl. move=> Hese.
    move: (Hese gd s1 vm1 (unzip1 [seq const_prop_e m i | i <- es]) v' (lest_to_les l') hvm1 Hess''). move=> [] x0 [] x1 Hn Hne Hnl. move: (sem_pexprs_to_sem_pexprs_e').
    move=> Hn'. move: (Hn' {| emem := emem s1; evm := vm1 |} gd (unzip1 [seq const_prop_e m i | i <- es]) (x0, x1) Hn). replace (p_globs p') with gd. move=> [] x2 [] /= Hex2 [] Hlx2 -> /=. move:  vuincl_exec_opn_eq. move=> Hex'. rewrite -Hex2.
    move: (Hex' o vs v' ves Hvv Hex). move=> Hex''.
    move:  vuincl_exec_opn_eq. move=> Hex1.
    move: (Hex1 o v' x0 ves Hnl Hex''). move=> -> /=.  rewrite hrvs in Hwe.
    rewrite /= in Hwe. rewrite Hwe /=.
    rewrite /= in Hse. rewrite /= in He. rewrite He in Hse.
    rewrite Hse. subst. rewrite /= in Hlee Hll Hlx2. rewrite hrvs in Hlee.
    rewrite /= in Hlee. admit. by rewrite p'_def /=. rewrite /= in Hse.
    rewrite /= in He. rewrite He in Hse. by rewrite Hse.
Admitted.

  (*move=> s1 s2 t o xs es H m ii Hm; apply: rbindP H => vs.
    apply: rbindP => ves Hes Ho Hw;move: (Hes) (Hw).
    move=> /(const_prop_esP Hm) [vs' Hes' Us] /(const_prop_rvsP Hm) [] /=.
    case: const_prop_rvs => m' rvs' /= h1 h2;split=>//.
    move=> vm1 hvm1.
    have [vm2 hw U]:= writes_uincl hvm1 (List_Forall2_refl _ value_uincl_refl) h2.
    exists vm2;split => //.
    apply sem_seq1; do 2 constructor.
    have [vs2 hs u2]:= sem_pexprs_uincl hvm1 Hes'.
    rewrite /sem_sopn hs /=.
    by have -> := vuincl_exec_opn_eq (Forall2_trans value_uincl_trans Us u2) Ho.
  Qed.*)

  Local Lemma Hif_true : sem_Ind_if_true_i p Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc He Hee Hc1 m ii Hm.
    move: (const_prop_eP). move=> Hcp.
    move: (Hcp gd e s1 m Hm (Vbool true) le He) =>
    [] x [] l' [] He' [] /= Hev /= Hel /=.
    case: (x) => // b {He}; subst.  case : is_boolP He'.
    Admitted.
   (* move => s1 s2 e c1 c2 He _ Hc1 m ii Hm.
    have  [v' [] ] /= := const_prop_eP Hm He.
    case: v' => // b {He} He ?;subst.
    case : is_boolP He => [b [] ->| {e} e He];first by apply Hc1.
    case: (Hc1 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;left.
    move=> vm1 /dup[] h /Hs [vm2 [ hc u]];exists vm2;split => //.
    apply sem_seq1; do 2 constructor=> //.
    by have [v2 -> /value_uincl_bool1 ->]:= sem_pexpr_uincl h He.
  Qed.*)

  Local Lemma Hif_false : sem_Ind_if_false_i p Pc Pi_r.
  Proof.
   Admitted.

  (* TODO: move this *)
  Lemma sem_seq1_iff (P : prog) (i : instr) (s1 s2 : estate):
     sem_I P s1 i s2 <-> sem P s1 [:: i] s2.
  Proof.
    split; first by apply sem_seq1.
    by case/semE => ? [?] /semE ->.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' Hc1 Hc He Hc1' Hc' Hw1 Hw m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c0] /=.
    case Heq2: const_prop => [m_ c0'] /=.
    have eq1_1 : evm s1 = evm s1 [\ww] by done.
    have /Hc:= valid_cpm_rm eq1_1 Hm;rewrite -/m' Heq1 /= => -[Hm'' Hc0].
    have := Hc' _ Hm'';rewrite Heq2 /= => -[_ Hc0'].
    have eq1_3 : evm s1 = evm s3 [\ww].
    + rewrite /ww write_i_while -write_c_app;apply: writeP.
      by apply: sem_app;eauto.
    have /Hw -/(_ ii) /=:= valid_cpm_rm eq1_3 Hm.
    have H1 := remove_cpm2 m ww.
    have /= : Mvarc_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile a c e c'))) c)
               (m'', c0).
    + by have := const_prop_m H1 (refl_equal c); rewrite Heq1.
    case: const_prop  => m2'' c2 [].
    rewrite /RelationPairs.RelCompFun /= => Hm2'' ->.
    have /= : Mvarc_eq (const_prop const_prop_i m2'' c') (m_, c0').
    + by have := const_prop_m Hm2'' (refl_equal c'); rewrite Heq2.
    case: const_prop  => ? c2' [].
    rewrite /RelationPairs.RelCompFun /= => _ -> -[Hs4 Hsem];split.
    by apply (valid_cpm_m (refl_equal (evm s4)) Hm2'').
    move: Hsem .
    have -> : const_prop_e m2'' e = const_prop_e m'' e.
    + by rewrite Hm2''.
    move=> Hrec vm1 hvm1.
    have [v' [ /=]]:= const_prop_eP Hm'' He.
    case: v' => //= ? Hv' ?;subst.
    have [vm2 [hc0 hvm2]]:= Hc0 _ hvm1.
    have [vm3 [hc0' hvm3]]:= Hc0' _ hvm2.
    have H :  forall e0,
      sem_pexpr gd s2 e0 = ok (Vbool true) ->
      (exists vm2,
        sem p' {| emem := emem s3; evm := vm3 |} [:: MkI ii (Cwhile a c0 e0 c0')]
           {| emem := emem s4; evm := vm2 |} ∧ vm_uincl (evm s4) vm2) ->
      exists vm2,
        sem p' {| emem := emem s1; evm := vm1 |} [:: MkI ii (Cwhile a c0 e0 c0')]
           {| emem := emem s4; evm := vm2 |} ∧ vm_uincl (evm s4) vm2.
    + move=> e0 He0 [vm5] [] /sem_seq1_iff /sem_IE Hsw hvm5;exists vm5;split => //.
      apply:sem_seq1;constructor.
      apply: (Ewhile_true hc0 _ hc0' Hsw).
      by have [b -> /value_uincl_bool1 ->]:= sem_pexpr_uincl hvm2 He0.
    by case:is_boolP Hv' (Hrec _ hvm3) => [? [->]| e0 He0]; apply H.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' Hc1 Hc He m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c0] /=.
    case Heq2: const_prop => [m_ c0'] /=.
    have eq1_1 : evm s1 = evm s1 [\ww] by done.
    have /Hc:= valid_cpm_rm eq1_1 Hm;rewrite -/m' Heq1 /= => -[Hm'' Hc0];split => //.
    have [v' [Hv' /=]]:= const_prop_eP Hm'' He.
    case: v' Hv' => // ? Hv' ? ;subst.
    case:is_boolP Hv' => [ ?[->] //| e0 He0].
    move=> vm1 /Hc0 [vm2 [hsem h]];exists vm2;split => //.
    apply: sem_seq1;constructor;apply: Ewhile_false => //.
    by have [v2 -> /value_uincl_bool1 ->]:= sem_pexpr_uincl h He0.
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hc Hfor m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    have Heqm: Mvar_eq m' (remove_cpm m' (Sv.union (Sv.singleton i) (write_c c))).
    + by have := remove_cpm2 m ww; rewrite /m' /ww write_i_for => ->.
    have := Hfor _ Heqm Hm'1.
    case Heq1: const_prop => [m'' c'] /= Hsem;split.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);econstructor;eauto.
    move=> vm1 /dup[] hvm1 /Hsem [vm2 [ hfor hvm2]];exists vm2;split => //.
    apply sem_seq1;constructor;econstructor;eauto.
    + have [v' [h /=]] := const_prop_eP Hm Hlo; case: v' h => //= ? h ->.
      by have [v2 -> /value_uincl_int1 ->]:= sem_pexpr_uincl hvm1 h.
    have [v' [h /=]] := const_prop_eP Hm Hhi;case: v' h => //= ? h ->.
    by have [v2 -> /value_uincl_int1 ->]:= sem_pexpr_uincl hvm1 h.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c m Hm hv vm1 hvm1;exists vm1;split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move => s1 s1' s2 s3 i w ws c Hw Hsemc Hc Hsemf Hf m Heqm Hm vm1 hvm1.
    have Hm' : valid_cpm (evm s1') m.
    + have Hmi : Mvar_eq m (Mvar.remove m i).
      + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //].
        rewrite Heqm;move: (remove_cpm_spec m (Sv.union (Sv.singleton i) (write_c c)) i).
        by case: Mvar.get => // a [];SvD.fsetdec.
      have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
      by apply: remove_cpm1P Hw Hm.
    have [_  Hc']:= Hc _ Hm'.
    have /(Hf _ Heqm) Hc'': valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec.
    have /(_ _ (value_uincl_refl _))[vm1' hw hvm1']:= write_var_uincl hvm1 _ Hw.
    have [vm2 [hc' /Hc'' [vm3 [hfor U]]]]:= Hc' _ hvm1';exists vm3;split => //.
    by apply: EForOne hc' hfor.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfun Hvs m ii' Hm.
    have [vargs' Hargs' Hall] := const_prop_esP Hm Hargs.
    have /(_ _ Hm) [] /=:= const_prop_rvsP _ Hvs.
    case: const_prop_rvs => m' rvs' /= ? hw;split=>//.
    move=> vm1 hvm1.
    have [vargs'' hargs'' U] := sem_pexprs_uincl hvm1 Hargs'.
    have [res' [hsem hres']]:= Hfun _ (Forall2_trans value_uincl_trans Hall U).
    have /(_ _ hvm1) [vm2 /= hw' hu] := writes_uincl _ hres' hw.
    exists vm2; split => //.
    by apply sem_seq1;constructor;econstructor;eauto.
  Qed.

(*  Lemma mapM2_truncate_val_uincl_a ts v1 v2 v1' :
    List.Forall2 value_uincl_a v1 v2 →
    mapM2 ErrType truncate_val ts v1 = ok v1' →
    mapM2 ErrType truncate_val ts v2 = ok v1'.
  Proof.
    move=> hall;elim: hall ts v1' => {v1 v2} [ | v1 v2 vs1 vs2 hv hall hrec];case => //= t ts v1'.
    by t_xrbindP => v' /(truncate_value_uincl_a hv) -> vs' /hrec -> /= <-.
  Qed. *)

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres'.
    case: f=> fi ftin fparams fc ftout fres /= Hget Hargs Hw _ Hc Hres Hfull.
    have := (@get_map_prog const_prop_fun p fn);rewrite Hget /=.
    have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
    move=> /Hc [];case: const_prop => m c' /= hcpm hc' hget vargs1 hargs'.
    have [vargs1' htr hu1]:= mapM2_truncate_val Hargs hargs'.
    have [vm3 /= hw hu3]:= write_vars_uincl (vm_uincl_refl _) hu1 Hw.
    have [vm4 /= []hc hu4]:= hc' _ hu3.
    have [vres1 hvres1 hu5]:= get_vars_uincl hu4 Hres.
    have [vres1' ??]:= mapM2_truncate_val Hfull hu5.
    exists vres1';split => //.
    econstructor;eauto => /=.
  Qed.

  Lemma const_prop_callP f mem mem' va va' vr:
    sem_call p mem f va mem' vr ->
    List.Forall2 value_uincl va va' ->
    exists vr', sem_call p' mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) h.
    apply h.
  Qed.

End PROOF.
