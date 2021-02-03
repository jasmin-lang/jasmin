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

Section Section.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Section GLOB_DEFS.

Context (gd: glob_decls).

Definition eqok_w (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v -> sem_pexpr gd st e2 = ok v.

Definition eqok (e1 e2:pexpr) st :=
  forall v, sem_pexpr gd st e1 = ok v ->
    exists v', sem_pexpr gd st e2 = ok v' /\ value_uincl v v'.

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

Hint Resolve eeq_refl eeq_w_refl : core.

Lemma eeq_weaken e1 e2 : eeq_w e1 e2 -> e1 =E e2.
Proof. by move=> h ?;apply eqok_weaken;apply h. Qed.

Lemma sint_of_wordP sz e : Papp1 (Oint_of_word sz) e =E sint_of_word sz e.
Proof.
  rewrite /sint_of_word => s.
  case: (is_wconst _ _) (@is_wconstP gd s sz e); last by move => _ ?; eauto.
  move => w /(_ _ erefl); t_xrbindP => v ok_v ok_w v'.
  rewrite /= /sem_sop1 /= ok_v /= ok_w => - [<-{v'}]; eauto.
Qed.

Lemma ssign_extendP sz sz' e : Papp1 (Osignext sz sz') e =E ssign_extend sz sz' e.
Proof.
  rewrite /ssign_extend => s.
  case: (is_wconst _ _) (@is_wconstP gd s sz' e); last by move => _ ?; eauto.
  move => w /(_ _ erefl); t_xrbindP => v ok_v ok_w v' /=.
  rewrite /sem_sop1 /= ok_v /= ok_w => - [<-{v'}].
  rewrite wrepr_unsigned; eauto.
Qed.

Lemma szero_extendP sz sz' e : Papp1 (Ozeroext sz sz') e =E szero_extend sz sz' e.
Proof.
  rewrite /szero_extend => s.
  case: (is_wconst _ _) (@is_wconstP gd s sz' e); last by move => _ ?; eauto.
  move => w /(_ _ erefl); t_xrbindP => v ok_v ok_w v' /=.
  rewrite /sem_sop1 /= ok_v /= ok_w => - [<-{v'}].
  rewrite wrepr_unsigned; eauto.
Qed.

Lemma snot_boolP e : Papp1 Onot e =E snot_bool e.
Proof.
  apply: eeq_weaken.
  case: e=> //=;try auto; first by move=> ???.
  move=> []; auto.
  move=> p rho v /=;rewrite /eqok.
  apply: rbindP => w;apply:rbindP => w' /= ->.
  apply: rbindP => /= b Hb [<-].
  rewrite /sem_sop1 /= negbK => [<-].
  by case: w' Hb => //= [? [->] | []].
Qed.

Lemma snot_wP sz e : Papp1 (Olnot sz) e =E snot_w sz e.
Proof.
apply: eeq_weaken; rewrite /snot_w; case heq: is_wconst => [ w | ] // s v /=.
by rewrite /= -bindA (is_wconstP gd s heq) /= => -[<-]; rewrite /sem_sop1 /= wrepr_unsigned.
Qed.

Lemma sneg_intP e : Papp1 (Oneg Op_int) e =E sneg_int e.
Proof.
apply: eeq_weaken; case: e => // [ z s v [] <- // | [] ] // [] // e s v /=; t_xrbindP => ? ? -> /=.
rewrite /sem_sop1; t_xrbindP => ? /of_val_int -> <- /= ? [<-] <-.
by rewrite Z.opp_involutive.
Qed.

Lemma sneg_wP sz e : Papp1 (Oneg (Op_w sz)) e =E sneg_w sz e.
Proof.
apply: eeq_weaken; rewrite /sneg_w; case heq: is_wconst => [ w | ] // s v /=.
by rewrite /= -bindA (is_wconstP gd s heq) /= => -[<-]; rewrite /sem_sop1 /= wrepr_unsigned.
Qed.

Lemma s_op1P o e : Papp1 o e =E s_op1 o e.
Proof.
  case: o => [?|?|??|??||?|[|?]];
  eauto using sint_of_wordP, ssign_extendP, szero_extendP,
    snot_boolP, snot_wP, sneg_intP, sneg_wP.
Qed.

(* * -------------------------------------------------------------------- *)

Lemma sandP e1 e2 : Papp2 Oand e1 e2 =E sand e1 e2.
Proof.
  apply: eeq_weaken; rewrite /sand.
  case: is_boolP => [b1 rho v /=| {e1} e1].
  + apply: rbindP=> v2' /= He2;apply:rbindP=> ? [<-].
    by apply: rbindP => b2 /to_boolI Hb2 [<-];subst v2';case:b1.
  case: is_boolP => [b2 rho v /=|{e2}e2];last by auto using eeq_refl.
  apply: rbindP => v1 Hv1;apply:rbindP=> b1 /to_boolI ?;subst v1 => /= -[<-].
  by case:b2;rewrite ?andbT ?andbF.
Qed.

Lemma sorP e1 e2 : Papp2 Oor e1 e2 =E sor e1 e2.
Proof.
  apply: eeq_weaken; rewrite /sor.
  case: is_boolP => [b1 rho v /=| {e1} e1].
  + apply: rbindP=> v2' /= He2;apply:rbindP=> ? [<-].
    by apply: rbindP => b2 /to_boolI Hb2 [<-];subst v2';case:b1.
  case: is_boolP => [b2 rho v /=|{e2}e2];last by auto using eeq_refl.
  apply: rbindP => v1 Hv1;apply:rbindP=> b1 /to_boolI ?;subst v1 => /= -[<-].
  by case:b2;rewrite ?orbT ?orbF.
Qed.

Lemma sadd_intP e1 e2 : Papp2 (Oadd Op_int) e1 e2 =E sadd_int e1 e2.
Proof.
  apply: eeq_weaken; rewrite /sadd_int; case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  + apply: rbindP => v2 Hv2; rewrite /sem_sop2 /=.
    apply: rbindP => z2 /of_val_int ? /=;subst v2=> [<-].
    by case: eqP => [-> // | /= _];rewrite Hv2.
  apply: rbindP => v1 Hv1;rewrite /sem_sop2 /=.
  apply: rbindP => z1 /of_val_int ? /=;subst v1=> [<-].
  by case: eqP => [-> // | /= _];rewrite Hv1 //= Z.add_0_r.
Qed.

Local Hint Resolve value_uincl_zero_ext : core.

Lemma sadd_wP sz e1 e2 : Papp2 (Oadd (Op_w sz)) e1 e2 =E sadd_w sz e1 e2.
Proof.
rewrite /sadd_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] //.
+ move => s v /=; rewrite /sem_sop2 /sem_sop1 /=.
  have := is_wconstP gd s h2; have := is_wconstP gd s h1.
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
+ case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
  have := is_wconstP gd s h1.
  t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
  have [sz' [w' [? ? ?]]] := of_val_word k6; subst.
  by rewrite GRing.add0r k4;eauto.
case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
have := is_wconstP gd s h2.
t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
have [sz' [w' [? ? ?]]] := of_val_word k5; subst.
by rewrite GRing.addr0 k3;eauto.
Qed.

Lemma saddP ty e1 e2 : Papp2 (Oadd ty) e1 e2 =E sadd ty e1 e2.
Proof. by case: ty; eauto using sadd_intP, sadd_wP. Qed.

Lemma ssub_intP e1 e2 : Papp2 (Osub Op_int) e1 e2 =E ssub_int e1 e2.
Proof.
  apply: eeq_weaken; rewrite /ssub_int.
  case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  apply: rbindP => v1 Hv1;rewrite /sem_sop2 /=.
  apply: rbindP => z1 /of_val_int ? /=;subst v1=> [<-].
  by case: eqP => [-> | /= _];rewrite Hv1 ?Z.sub_0_r.
Qed.

Lemma ssub_wP sz e1 e2 : Papp2 (Osub (Op_w sz)) e1 e2 =E ssub_w sz e1 e2.
Proof.
rewrite /ssub_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] //.
+ move => s v /=; rewrite /sem_sop2 /sem_sop1 /=.
  have := is_wconstP gd s h2; have := is_wconstP gd s h1.
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
have := is_wconstP gd s h2.
t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
have [sz' [w' [? ? ?]]] := of_val_word k5; subst.
by rewrite GRing.subr0 k3;eauto.
Qed.

Lemma ssubP ty e1 e2 : Papp2 (Osub ty) e1 e2 =E ssub ty e1 e2.
Proof. by case: ty; eauto using ssub_intP, ssub_wP. Qed.

Lemma smul_intP e1 e2 : Papp2 (Omul Op_int) e1 e2 =E smul_int e1 e2.
Proof.
  apply: eeq_weaken; rewrite /smul_int.
  case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  + apply: rbindP => v2 Hv2. rewrite /sem_sop2 /=.
    apply: rbindP => z2 /of_val_int ?;subst v2.
    case:eqP => [-> //|_]; case:eqP => [-> | _ /=];last by rewrite Hv2.
    by rewrite Z.mul_1_l => -[<-].
  apply: rbindP => v1 Hv1. rewrite /sem_sop2 /=.
  apply: rbindP => z1 /of_val_int ?;subst v1.
  case:eqP => [->|_] <-;first by rewrite  Z.mul_0_r.
  case:eqP => [-> | _ /=];first by rewrite Z.mul_1_r.
  by rewrite Hv1.
Qed.

Lemma smul_wP sz e1 e2 : Papp2 (Omul (Op_w sz)) e1 e2 =E smul_w sz e1 e2.
Proof.
rewrite /smul_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] //.
+ move => s v /=; rewrite /sem_sop2 /sem_sop1 /=.
  have := is_wconstP gd s h2; have := is_wconstP gd s h1.
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
+ case: eqP => hn1; [| case: eqP => hn2] => s v /=; rewrite /sem_sop2 /sem_sop1 /=;
  have := is_wconstP gd s h1; t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 ?; clarify.
  - rewrite wrepr_unsigned GRing.mul0r;eauto.
  - case: (of_val_word k6) => {k6} sz' [w] [? ? ?]; subst.
    by rewrite k4 GRing.mul1r; eauto.
  by rewrite k4 /= k6 /= wrepr_unsigned truncate_word_u /=;eexists;split;eauto => /=.
case: eqP => hn1; [| case: eqP => hn2] => s v /=; rewrite /sem_sop2 /sem_sop1 /=;
have := is_wconstP gd s h2; t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 ?; clarify.
- by rewrite wrepr_unsigned GRing.mulr0;eauto.
- case: (of_val_word k5) => {k5} sz' [w] [? ? ?]; subst.
  by rewrite k3 GRing.mulr1;eauto.
by rewrite k3 /= k5 /= truncate_word_u wrepr_unsigned /=;eexists;split;eauto => /=.
Qed.

Lemma smulP ty e1 e2 : Papp2 (Omul ty) e1 e2 =E smul ty e1 e2.
Proof. by case: ty; eauto using smul_intP, smul_wP. Qed.

Lemma s_eqP ty e1 e2 : Papp2 (Oeq ty) e1 e2 =E s_eq ty e1 e2.
Proof.
  rewrite /s_eq;case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;case: sem_pexpr => //= ve.
    rewrite /sem_sop2; case: ty => [ | sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.eqb_refl.
    by rewrite eqxx.
  case: ty.
  + apply: eeq_weaken.
    case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  move => sz.
  case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] // s v;
  rewrite /= /sem_sop2;
  t_xrbindP => v1 k1 v2 k2 w1' /of_val_word [sz1] [w1] [hle1 ? ?]
                  w2' /of_val_word [sz2 [w2 [hle2 ? ?]]] ? /= [] ? ?;subst.
  eexists; split; first reflexivity.
  have := is_wconstP gd s h1; rewrite k1 /= /truncate_word hle1 => -[?]; subst.
  have := is_wconstP gd s h2; rewrite k2 /= /truncate_word hle2 => -[?]; subst.
  done.
Qed.

Lemma sneqP ty e1 e2 : Papp2 (Oneq ty) e1 e2 =E sneq ty e1 e2.
Proof.
  rewrite /sneq /s_eq.
  case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;case: sem_pexpr => //= ve.
    rewrite /sem_sop2; case: ty => [ | sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.eqb_refl.
    by rewrite eqxx.
  case: ty.
  + apply: eeq_weaken.
    case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  move => sz.
  case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] // s v;
  rewrite /= /sem_sop2;
  t_xrbindP => v1 k1 v2 k2 w1' /of_val_word [sz1] [w1] [hle1 ? ?]
                  w2' /of_val_word [sz2 [w2 [hle2 ? ?]]] ? /= [] ? ?;subst.
  eexists; split; first reflexivity.
  have := is_wconstP gd s h1; rewrite k1 /= /truncate_word hle1 => -[?]; subst.
  have := is_wconstP gd s h2; rewrite k2 /= /truncate_word hle2 => -[?]; subst.
  done.
Qed.

Lemma is_cmp_constP s ty e z :
  is_cmp_const ty e = Some z →
  match ty with
  | Cmp_int => e = Pconst z
  | Cmp_w sg sz =>
    exists2 x,
    sem_pexpr gd s e = ok x &
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
  t_xrbindP => v -> ok_w [<-{z}].
  exists v => //.
  exists w => //.
  by case: sg.
Qed.

Ltac is_cmp_const s :=
  match goal with
  | |- context[ is_cmp_const ?ty ?e ] =>
    case: is_cmp_const (@is_cmp_constP s ty e);
    [ let n := fresh in move => n /(_ _ erefl); move: n | ]
  end.

Lemma sltP ty e1 e2 : Papp2 (Olt ty) e1 e2 =E slt ty e1 e2.
Proof.
  rewrite /slt;case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    rewrite /sem_sop2; case: ty => [ | sg sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.ltb_irrefl.
    by rewrite wlt_irrefl.
  apply: eeq_weaken => s.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n1 h1.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n2.
  case: ty h1.
  + move => -> ->; exact: eeq_w_refl.
  move => sg sz [] v1 ok_v1 [] w1 ok_w1 h1 [] v2 ok_v2 [] w2 ok_w2.
  by case: sg h1 => <- <- v;
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= ssrZ.ltzE.
Qed.

Lemma sleP ty e1 e2 : Papp2 (Ole ty) e1 e2 =E sle ty e1 e2.
Proof.
  rewrite /sle; case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    rewrite /sem_sop2; case: ty => [ | sg sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.leb_refl.
    by rewrite wle_refl.
  apply: eeq_weaken => s.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n1 h1.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n2.
  case: ty h1.
  + move => -> ->; exact: eeq_w_refl.
  move => sg sz [] v1 ok_v1 [] w1 ok_w1 h1 [] v2 ok_v2 [] w2 ok_w2.
  by case: sg h1 => <- <- v;
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= ssrZ.lezE.
Qed.

Lemma sgtP ty e1 e2 : Papp2 (Ogt ty) e1 e2 =E sgt ty e1 e2.
Proof.
  rewrite /sgt;case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    rewrite /sem_sop2; case: ty => [ | sg sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.gtb_ltb Z.ltb_irrefl.
    by rewrite wlt_irrefl.
  apply: eeq_weaken => s.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n1 h1.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n2.
  case: ty h1.
  + move => -> ->; exact: eeq_w_refl.
  move => sg sz [] v1 ok_v1 [] w1 ok_w1 h1 [] v2 ok_v2 [] w2 ok_w2.
  by case: sg h1 => <- <- v;
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= Z.gtb_ltb ssrZ.ltzE.
Qed.

Lemma sgeP ty e1 e2 : Papp2 (Oge ty) e1 e2 =E sge ty e1 e2.
Proof.
  rewrite /sge; case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    rewrite /sem_sop2; case: ty => [ | sg sz ] /=; t_xrbindP => ? -> ? [<-] <-;
    (eexists; split; first reflexivity).
    - by rewrite Z.geb_leb Z.leb_refl.
    by rewrite wle_refl.
  apply: eeq_weaken => s.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n1 h1.
  is_cmp_const s; last by move => _; exact: eeq_w_refl.
  move => n2.
  case: ty h1.
  + move => -> ->; exact: eeq_w_refl.
  move => sg sz [] v1 ok_v1 [] w1 ok_w1 h1 [] v2 ok_v2 [] w2 ok_w2.
  by case: sg h1 => <- <- v;
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= Z.geb_leb ssrZ.lezE.
Qed.

Lemma sbitwP i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 :
  (∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
      sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v →
      v = Vword (z sz (zero_extend sz w1) (zero_extend sz w2))) →
  Papp2 (i sz) e1 e2 =E sbitw i z sz e1 e2.
Proof.
rewrite /sbitw => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] //.
move => s v /=; t_xrbindP => v1 k1 v2 k2 hv.
rewrite /sem_sop1 /= wrepr_unsigned.
eexists; split; first reflexivity.
have := is_wconstP gd s h1; rewrite k1 => /of_val_word [sz1] [w1] [hle1 ??]; subst.
have := is_wconstP gd s h2; rewrite k2 => /of_val_word [sz2] [w2] [hle2 ??]; subst.
by rewrite (h _ _ _ _ _ hv).
Qed.

Lemma slandP ty e1 e2 : Papp2 (Oland ty) e1 e2 =E sland ty e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma slorP ty e1 e2  : Papp2 (Olor ty) e1 e2 =E slor ty e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma slxorP ty e1 e2 : Papp2 (Olxor ty) e1 e2 =E slxor ty e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma sbitw8P i (z: ∀ sz, word sz → word U8 → word sz) sz e1 e2 :
  (∀ sz1 (w1: word sz1) sz2 (w2: word sz2) v,
      sem_sop2 (i sz) (Vword w1) (Vword w2) = ok v →
      v = Vword (z sz (zero_extend sz w1) (zero_extend U8 w2))) →
  Papp2 (i sz) e1 e2 =E sbitw8 i z sz e1 e2.
Proof.
rewrite /sbitw8 => h.
case h1: is_wconst => [ n1 | ] //.
case h2: is_wconst => [ n2 | ] //.
move => s v /=; t_xrbindP => v1 k1 v2 k2 hv.
rewrite /sem_sop1 /= wrepr_unsigned.
eexists; split; first reflexivity.
have := is_wconstP gd s h1; rewrite k1 => /of_val_word [sz1] [w1] [???]; subst.
have := is_wconstP gd s h2; rewrite k2 => /of_val_word [sz2] [w2] [???]; subst.
by rewrite (h _ _ _ _ _ hv).
Qed.

Lemma slslP sz e1 e2  : Papp2 (Olsl sz) e1 e2 =E sshl sz e1 e2.
Proof.
  apply: sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma slsrP sz e1 e2  : Papp2 (Olsr sz) e1 e2 =E sshr sz e1 e2.
Proof.
  apply: sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma sasrP sz e1 e2  : Papp2 (Oasr sz)  e1 e2 =E ssar sz e1 e2.
Proof.
  apply: sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma sdivP k e1 e2 : Papp2 (Odiv k) e1 e2 =E sdiv k e1 e2.
Proof.
  case: k => [ | u sz] /=.
  + rewrite /soint.
    case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v /=;eauto.
  rewrite /sbituw.
  case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  case:eqP => // neq s v.
  rewrite /= /sem_sop2 /= /mk_sem_divmod.
  t_xrbindP => v1 k1 v2 k2 w1' /of_val_word [sz1] [w1] [hle1 ? ?]
                  w2' /of_val_word [sz2] [w2] [hle2 ? ?] ?; subst.
  have := is_wconstP gd s h1; rewrite k1 /= /truncate_word hle1 => -[?]; subst.
  have := is_wconstP gd s h2; rewrite k2 /= /truncate_word hle2 => -[?]; subst.
  case: ifP => // _ [?] ?; subst.
  eexists; split; first reflexivity.
  by rewrite /sem_sop1 /= wrepr_unsigned;case: u.
Qed.

Lemma smodP k e1 e2 : Papp2 (Omod k) e1 e2 =E smod k e1 e2.
Proof.
  case: k => [ | u sz] /=.
  + rewrite /soint.
    case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v /=;eauto.
  rewrite /sbituw.
  case h1: is_wconst => [ n1 | ] //.
  case h2: is_wconst => [ n2 | ] //.
  case:eqP => // neq s v.
   rewrite /= /sem_sop2 /= /mk_sem_divmod.
  t_xrbindP => v1 k1 v2 k2 w1' /of_val_word [sz1] [w1] [hle1 ? ?]
                  w2' /of_val_word [sz2] [w2] [hle2 ? ?] ?; subst.
  have := is_wconstP gd s h1; rewrite k1 /= /truncate_word hle1 => -[?]; subst.
  have := is_wconstP gd s h2; rewrite k2 /= /truncate_word hle2 => -[?]; subst.
  case: ifP => // _ [?] ?; subst.
  eexists; split; first reflexivity.
  by rewrite /sem_sop1 /= wrepr_unsigned;case: u.
Qed.

Lemma svaddP ve ws e1 e2 : Papp2 (Ovadd ve ws) e1 e2 =E svadd ve ws e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma svsubP ve ws e1 e2 : Papp2 (Ovsub ve ws) e1 e2 =E svsub ve ws e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma svmulP ve ws e1 e2 : Papp2 (Ovmul ve ws) e1 e2 =E svmul ve ws e1 e2.
Proof.
  apply: sbitwP => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma svshlP ve ws e1 e2 : Papp2 (Ovlsl ve ws) e1 e2 =E svshl ve ws e1 e2.
Proof.
  apply: @sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma svshrP ve ws e1 e2 : Papp2 (Ovlsr ve ws) e1 e2 =E svshr ve ws e1 e2.
Proof.
  apply: @sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma svsarP ve ws e1 e2 : Papp2 (Ovasr ve ws) e1 e2 =E svsar ve ws e1 e2.
Proof.
  apply: @sbitw8P => sz1 w1 sz2 w2 v.
  apply: rbindP => v1 /truncate_wordP [_ ->].
  apply: rbindP => v2 /truncate_wordP [_ ->].
  by case.
Qed.

Lemma s_op2P o e1 e2 : Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case: o;eauto using sandP, sorP, saddP, smulP, ssubP, sdivP, smodP,
                      s_eqP, sneqP, sltP, sleP, sgtP, sgeP,
                      slandP, slorP, slxorP, slslP, slsrP, sasrP,
                      svaddP, svsubP, svmulP, svshlP, svshrP, svsarP.
Qed.

Lemma s_opNP op s es :
  sem_pexpr gd s (s_opN op es) = sem_pexpr gd s (PappN op es).
Proof.
  rewrite /s_opN.
  case hi: (mapM _ _) => [ i | ] //=.
  case heq: (sem_opN _ _) => [ v | ] //.
  case: v heq => // sz w'.
  case: op => sz' pe /=.
  rewrite /sem_opN /=; apply: rbindP => w h /ok_word_inj [] ?; subst => /= <-{w'}.
  rewrite /sem_sop1 /= wrepr_unsigned -/(sem_pexprs _ _).
  have -> /= : sem_pexprs gd s es = ok i.
  + elim: es i hi {h} => // - [] // z es ih /=; t_xrbindP => _ vs ok_vs <-.
    by rewrite (ih _ ok_vs).
  by rewrite h.
Qed.

Definition vconst c :=
  match c with
  | Cbool b => Vbool b
  | Cint z => Vint z
  | Cword sz z => Vword z
  end.

Definition valid_cpm (vm: vmap)  (m:cpm) :=
  forall x n, Mvar.get m x = Some n -> get_var vm x = ok (vconst n).

Definition eqoks e1 e2 st :=
  ∀ vs, sem_pexprs gd st e1 = ok vs → exists2 vs', sem_pexprs gd st e2 = ok vs' & List.Forall2 value_uincl vs vs'.

Section CONST_PROP_EP.
  Context (s:estate) m (Hvalid: valid_cpm (evm s) m).
  Let P e : Prop := e =[s] const_prop_e m e.
  Let Q es : Prop := eqoks es (map (const_prop_e m) es) s.

  Lemma const_prop_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; subst P Q; rewrite /eqok; split => /=;
    try (intros; clarify; eauto; fail).
    - by move => ? [<-]; exists [::].
    - move => e rec es ih ?; rewrite /sem_pexprs /=.
      apply: rbindP => v /rec [v'] [->] hu.
      by apply: rbindP => vs /ih{ih}; rewrite -/(sem_pexprs gd s _) => - [vs'] -> hrec [<-] /=; eauto.
    - move => [x []] v; rewrite /= /get_gvar /=; last by eauto.
      move: Hvalid => /(_ x).
      case: Mvar.get => [n /(_ _ erefl)| _ /= ]; last by rewrite /= /get_gvar /=;eauto.
      by case: n => [ b | n | sz w ] /= -> [<-]; rewrite /sem_sop1 /= ?wrepr_unsigned;
           eexists;(split;first reflexivity) => /=.
    - move => aa sz x e He v.
      apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
      t_xrbindP => z w /(He _) [v'] [->] /value_uincl_int h/h{h} [??];subst.
      move => a ha ?; subst; rewrite /= ha.
      by eexists; (split; first reflexivity) => /=.
    - move => aa sz len x e He v.
      apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
      t_xrbindP => z w /(He _) [v'] [->] /value_uincl_int h/h{h} [??];subst.
      move => a ha ?; subst; rewrite /= ha.
      by eexists; (split; first reflexivity) => /=.
    - move => sz x e He v.
      t_xrbindP => ? ? -> /= -> ? ? /He [v'] [->] /value_uincl_word h/h{h} /=.
      rewrite /to_pointer => -> /= ? -> <- /=.
      by eexists; ( split; first reflexivity ) => /=.
    - move => op e He v.
      t_xrbindP => v' /He [w] [hw hvw] h; apply /s_op1P.
      rewrite /= hw /=.
      by apply: vuincl_sem_sop1 h.
    - move => op e1 He1 e2 He2 v.
      t_xrbindP => v1 /He1 [w1] [hw1 hvw1] v2 /He2 [w2] [hw2 hvw2] h; apply/s_op2P.
      rewrite /= hw1 hw2 /=.
      by apply: vuincl_sem_sop2 h.
    - move => op es ih v.
      t_xrbindP => vs /ih{ih} [] vs' ih /vuincl_sem_opN h/h{h} [] v' ok_v' h.
      by rewrite s_opNP /= -/(sem_pexprs _ _) ih /= ok_v'; eauto.
    move => t e He e1 He1 e2 He2 v.
    t_xrbindP => b ve /He/= [] ve' [] hse hue /(value_uincl_bool hue) [??];subst.
    move=> ve1 vte1 /He1 []ve1' [] hse1 hue1 /(truncate_value_uincl hue1) [] ? /dup[] ht1 /value_uincl_truncate_val ht1' hu1.
    move=> ve2 vte2 /He2 []ve2' [] hse2 hue2 /(truncate_value_uincl hue2) [] ? /dup[] ht2 /value_uincl_truncate_val ht2' hu2 <-.
    rewrite /s_if; case: is_boolP hse; first by move=> [][<-] /=;eexists;split;eauto using value_uincl_trans.
    move=> /= p -> /=;rewrite hse1 hse2 /= ht1 ht2 /=;eexists;split;eauto.
    by case:(b).
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
  value_uincl v v1 ->
  truncate_val ty v = ok v' ->
  write_lval gd x v' s1 = ok s1' ->
  valid_cpm (evm s1') m ->
  valid_cpm (evm s1') (add_cpm m x tag ty e).
Proof.
  rewrite /add_cpm;case: x => //= x He.
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
  case: x => -[] [] //= szx xn vi; apply: rbindP => vm.
  apply: set_varP => //= w' [<-] <- [<-] /= Hv z /= n.
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
  valid_cpm (evm s1) m ->
  write_lval gd x v s1 = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rv m x).1 /\
  write_lval gd (const_prop_rv m x).2 v s1 = ok s2.
Proof.
  case:x => [ii t | x | sz x p | aa sz x p | aa sz len x p] /= Hv.
  + by move=> H; have [??]:= write_noneP H; subst s2.
  + by move=> H;split=>//;apply: remove_cpm1P H Hv.
  + apply: rbindP => z Hz;rewrite Hz /=.
    apply: rbindP => z'.
    apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) [] z3 [] -> /= /value_uincl_word h/h{h} ->.
    by apply: rbindP => w -> /=;apply: rbindP => m' -> [<-].
  + apply: on_arr_varP;rewrite /on_arr_var => n t Htx -> /=.
    apply: rbindP => z;apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) [] z3 [] ->.
    move => /value_uincl_int h/h{h} [] ??; subst.
    apply: rbindP => w -> /=;apply: rbindP => t' -> /=.
    apply: rbindP => vm Hvm [<-];rewrite Hvm;split=>//=.
    have H : write_var x (Varr t') s1 = ok (with_vm s1 vm) by rewrite /write_var Hvm.
    by apply: remove_cpm1P H Hv.
  apply: on_arr_varP;rewrite /on_arr_var => n t Htx -> /=.
  apply: rbindP => z;apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) [] z3 [] ->.
  move => /value_uincl_int h/h{h} [] ??; subst.
  apply: rbindP => w -> /=;apply: rbindP => t' -> /=.
  apply: rbindP => vm Hvm [<-];rewrite Hvm;split=>//=.
  have H : write_var x (Varr t') s1 = ok (with_vm s1 vm) by rewrite /write_var Hvm.
  by apply: remove_cpm1P H Hv.
Qed.

Lemma const_prop_rvsP s1 s2 m x v:
  valid_cpm (evm s1) m ->
  write_lvals gd s1 x v = Ok error s2 ->
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

Lemma remove_cpmP s s' m x v:
  write_lval gd x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv; apply: (valid_cpm_rm _ Hv);eapply vrvP;eauto. Qed.

End GLOB_DEFS.

Instance const_prop_e_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq) const_prop_e.
Proof.
  move=> m1 m2 Hm e e' <- {e'}.
  elim: e => //=.
  + by move=> ?;rewrite Hm.
  + by move=> ???? ->.
  + by move=> ????? ->.
  + by move=> ??? ->.
  + by move=> ?? ->.
  + by move=> ?? -> ? ->.
  + move => op es h; f_equal.
    elim: es h => // e es ih rec /=; f_equal.
    - by apply: rec; rewrite in_cons eqxx.
    by apply: ih => e' he'; apply: rec; rewrite in_cons he' orbT.
  by move=> ?? -> ? -> ? ->.
Qed.

Instance const_prop_rv_m :
  Proper (@Mvar_eq const_v ==> eq ==> RelationPairs.RelProd (@Mvar_eq const_v) eq) const_prop_rv.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => [ v | v | sz v p | aa sz v p | aa sz len v p] //=;rewrite Hm.
Qed.

Instance const_prop_rvs_m :
  Proper (@Mvar_eq const_v ==> eq ==> RelationPairs.RelProd (@Mvar_eq const_v) eq) const_prop_rvs.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  elim: rv m1 m2 Hm => //= rv rvs Hrec m1 m2 Hm.
  have [/=]:= const_prop_rv_m Hm (refl_equal rv).
  case: const_prop_rv => ??;case: const_prop_rv => ??.
  rewrite /RelationPairs.RelCompFun /= => /Hrec H ->.
  case: const_prop_rvs H => ??;case: const_prop_rvs => ?? [].
  by rewrite /RelationPairs.RelCompFun /= => -> ->.
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
  case: Mvar.get (remove_cpm_spec m1 s1 z) => [? |];
   case: Mvar.get (remove_cpm_spec m2 s2 z) => [? |] => //.
  + by rewrite Hm => -[] -> _ [[]] ->.
  + by rewrite Hm Hs => -[ -> | ? ] [].
  by rewrite Hm Hs => -[] -> ? [] .
Qed.

Definition Mvarc_eq T := RelationPairs.RelProd (@Mvar_eq T) (@eq cmd).

Section PROPER.

  Let Pr (i:instr_r) :=
    forall ii m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_ir m1 ii i) (const_prop_ir m2 ii i).

  Let Pi (i:instr) :=
    forall m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_i m1 i) (const_prop_i m2 i).

  Let Pc (c:cmd) :=
    forall m1 m2, Mvar_eq m1 m2 ->
    Mvarc_eq (const_prop const_prop_i m1 c) (const_prop const_prop_i m2 c).

  Local Lemma Wmk i ii: Pr i -> Pi (MkI ii i).
  Proof. by move=> Hi m1 m2;apply Hi. Qed.

  Local Lemma Wnil : Pc [::].
  Proof. by move=> m1 m2 /= ->. Qed.

  Local Lemma Wcons i c:  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> Hi Hc m1 m2 /= /Hi.
    case: const_prop_i => m1' i'; case: const_prop_i => m2' i'' [] /Hc.
    rewrite /RelationPairs.RelCompFun /=.
    case: const_prop => m1'' c'; case: const_prop => m2'' c'' [].
    by rewrite /RelationPairs.RelCompFun /= => -> -> ->.
  Qed.

  Local Lemma Wasgn x t ty e: Pr (Cassgn x t ty e).
  Proof.
    move=> ii m1 m2 /= Heq; have := const_prop_rv_m Heq (refl_equal x).
    case: const_prop_rv => ??;case: const_prop_rv => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    by split => //=; rewrite /RelationPairs.RelCompFun /= Heq.
  Qed.

  Local Lemma Wopn xs t o es: Pr (Copn xs t o es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.

  Local Lemma Wif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> Hc1 Hc2 ii m1 m2 Heq /=.
    have -> : const_prop_e m1 e = const_prop_e m2 e by rewrite Heq.
    case: is_bool=> [ [] | ].
    + by apply Hc1.
    + by apply Hc2.
    have := Hc1 _ _ Heq; have := Hc2 _ _ Heq.
    do 4 case const_prop => ??.
    move=> [];rewrite /RelationPairs.RelCompFun /= => -> ->.
    by move=> [];rewrite /RelationPairs.RelCompFun /= => -> ->.
  Qed.

  Local Lemma Wfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof.
    move=> Hc ii m1 m2 Heq /=.
    have -> : const_prop_e m1 lo = const_prop_e m2 lo by rewrite Heq.
    have -> : const_prop_e m1 hi = const_prop_e m2 hi by rewrite Heq.
    set ww1 := remove_cpm _ _; set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => ??; case: const_prop => ?? [].
    by rewrite /RelationPairs.RelCompFun /= Hw => _ ->.
  Qed.

  Local Lemma Wwhile a c e c': Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> Hc Hc' ii m1 m2 Heq /=.
    set ww1 := remove_cpm _ _;set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => m1' c1. case: const_prop => m2' c2 [].
    rewrite /RelationPairs.RelCompFun /= => H ->.
    move: (H) => /Hc'; case: const_prop => ?? ; case: const_prop => ?? [].
    rewrite /RelationPairs.RelCompFun /= => _ ->.
    have -> : const_prop_e m1' e = const_prop_e m2' e by rewrite H.
    by case: is_bool => //= ?; case:ifP.
  Qed.

  Local Lemma Wcall i xs f es: Pr (Ccall i xs f es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.

  Local Lemma Wcopy x1 e1: Pr (Ccopy x1 e1).
  Proof.
    move => ii m1 m2 Heq /=.
    have -> : const_prop_e m1 e1 = const_prop_e m2 e1 by rewrite Heq.
    have []:= const_prop_rv_m Heq (refl_equal x1).
    rewrite /RelationPairs.RelCompFun.
    case: const_prop_rv => /= [m1' rv1'].
    case: const_prop_rv => /= [m2' rv2'].
    by move => Heq' <-; split.
  Qed.

End PROPER.

Lemma const_prop_i_m :
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) const_prop_i.
Proof.
  move=> m1 m2 Hm i1 i2 <-.
  apply : (instr_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall Wcopy i1) Hm.
Qed.

Lemma const_prop_i_r_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq ==> @Mvarc_eq const_v) const_prop_ir.
Proof.
  move=> m1 m2 Hm ii1 ii2 <- i1 i2 <-.
  apply : (instr_r_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall Wcopy i1) Hm.
Qed.

Lemma const_prop_m :
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) (const_prop const_prop_i).
Proof.
  move=> m1 m2 Hm c1 c2 <-.
  apply : (cmd_rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall Wcopy c1) Hm.
Qed.

Lemma valid_cpm_m :
  Proper (eq ==> @Mvar_eq const_v ==> iff) valid_cpm.
Proof.
  move=> s? <- m m' Hm;split => H z n Hget;apply H.
  by rewrite Hm. by rewrite -Hm.
Qed.

Section PROOF.

  Variable (p:prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Let p' := const_prop_prog p.

  Let Pi s1 i s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) (const_prop_i m i).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' ev (with_vm s1 vm1) (const_prop_i m i).2 (with_vm s2 vm2) /\
          vm_uincl (evm s2) vm2.

  Let Pi_r s1 i s2 :=
    forall m ii,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) (const_prop_ir m ii i).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' ev (with_vm s1 vm1) (const_prop_ir m ii i).2 (with_vm s2 vm2) /\
          vm_uincl (evm s2) vm2.

  Let Pc s1 c s2 :=
    forall m,
      valid_cpm s1.(evm) m ->
      valid_cpm s2.(evm) (const_prop const_prop_i m c).1 /\
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
          sem p' ev (with_vm s1 vm1) (const_prop const_prop_i m c).2 (with_vm s2 vm2) /\
          vm_uincl (evm s2) vm2.

  Let Pfor (i:var_i) zs s1 c s2 :=
    forall m,
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s1.(evm) m ->
      forall vm1,
        vm_uincl (evm s1) vm1 ->
        exists vm2,
         sem_for p' ev i zs (with_vm s1 vm1) (const_prop const_prop_i m c).2 (with_vm s2 vm2) /\
         vm_uincl (evm s2) vm2.

  Let Pfun m1 fd vargs m2 vres :=
    forall vargs',
      List.Forall2 value_uincl vargs vargs' ->
      exists vres',
        sem_call p' ev m1 fd vargs' m2 vres' /\
        List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    by move=> s m /= ?;split=>// vm1 hu1;exists vm1;split => //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc m /Hi [] /=.
    case: const_prop_i => m' i' /Hc [].
    case: const_prop => m'' c' /= Hm'' Hc' Hi';split => //.
    move=> vm1 /Hi' [vm2 [hi /Hc']] [vm3 [hc ?]];exists vm3;split => //.
    by apply: sem_app hi hc.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi m /(Hi _ ii). Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
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
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H m ii Hm; apply: rbindP H => vs.
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
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 He _ Hc1 m ii Hm.
    have  [v' [] ] /= := const_prop_eP Hm He.
    case: v' => // b {He} He ?;subst.
    case : is_boolP He => [b [] ->| {e} e He];first by apply Hc1.
    case: (Hc1 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;left.
    move=> vm1 /dup[] h /Hs [vm2 [ hc u]];exists vm2;split => //.
    apply sem_seq1; do 2 constructor=> //.
    by have [v2 -> /value_uincl_bool1 ->]:= sem_pexpr_uincl h He.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 He _ Hc1 m ii Hm.
    have  [v' [] ] /= := const_prop_eP Hm He.
    case: v' => // b {He} He ?;subst.
    case : is_boolP He => [b [] ->| {e} e He];first by apply Hc1.
    case: (Hc1 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;right.
    move=> vm1 /dup[] h /Hs [vm2 [ hc u]];exists vm2;split => //.
    apply sem_seq1; constructor;apply Eif_false => //.
    by have [v2 -> /value_uincl_bool1 ->]:= sem_pexpr_uincl h He.
  Qed.

  (* TODO: move this *)
  Lemma sem_seq1_iff (P : prog) (Ev: extra_val_t) (i : instr) s1 s2:
     sem_I P Ev s1 i s2 <-> sem P Ev s1 [:: i] s2.
  Proof.
    split; first by apply sem_seq1.
    by case/semE => ? [?] /semE ->.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
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
        sem p' ev (with_vm s3 vm3) [:: MkI ii (Cwhile a c0 e0 c0')] (with_vm s4 vm2) ∧ 
        vm_uincl (evm s4) vm2) ->
      exists vm2,
        sem p' ev (with_vm s1 vm1) [:: MkI ii (Cwhile a c0 e0 c0')] (with_vm s4 vm2)  ∧ 
        vm_uincl (evm s4) vm2.
    + move=> e0 He0 [vm5] [] /sem_seq1_iff /sem_IE Hsw hvm5;exists vm5;split => //.
      apply:sem_seq1;constructor.
      apply: (Ewhile_true hc0 _ hc0' Hsw).
      by have [b -> /value_uincl_bool1 ->]:= sem_pexpr_uincl hvm2 He0.
    by case:is_boolP Hv' (Hrec _ hvm3) => [? [->]| e0 He0]; apply H.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
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

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hc Hfor m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    have Heqm: Mvar_eq m' (remove_cpm m' (Sv.union (Sv.singleton i) (write_c c))).
    + by have := remove_cpm2 m ww; rewrite /m' /ww write_i_for => ->.
    have := Hfor _ Heqm Hm'1.
    case Heq1: const_prop => [m'' c'] /= Hsem;split.
    + by apply: valid_cpm_rm Hm;apply (write_iP (P:=p) (ev:=ev));econstructor;eauto.
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

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
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

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
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

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
    case: f=> fi ftin fparams fc ftout fres fex /= Hget Hargs Hi Hw _ Hc Hres Hfull Hfi.
    have := (get_map_prog const_prop_fun p fn);rewrite Hget /=.
    have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
    move=> /Hc [];case: const_prop => m c' /= hcpm hc' hget vargs1 hargs'.
    have [vargs1' htr hu1]:= mapM2_truncate_val Hargs hargs'.
    have [vm3 /= hw hu3]:= write_vars_uincl (vm_uincl_refl _) hu1 Hw.
    have [vm4 /= []hc hu4]:= hc' _ hu3.
    have [vres1 hvres1 hu5]:= get_vars_uincl hu4 Hres.
    have [vres1' ??]:= mapM2_truncate_val Hfull hu5.
    exists vres1';split => //.
    econstructor;eauto => /=.
    by move: hw;rewrite with_vm_same.
  Qed.

  Lemma const_prop_callP f mem mem' va va' vr:
    sem_call p ev mem f va mem' vr ->
    List.Forall2 value_uincl va va' ->
    exists vr', sem_call p' ev mem f va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) h.
    apply h.
  Qed.

End PROOF.

End Section.
