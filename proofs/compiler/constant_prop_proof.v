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

Definition array_eq v1 v2 := 
   if type_of_val v1 is sarr _ _ then v1 = v2 else True.

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
  case: ty v1' => [||s n|s] v1' [U Aeq];t_xrbindP.
  + by move=> /(of_val_uincl U) /= [b [-> ]]; rewrite /val_uincl /= => ->.
  + by move=> /(of_val_uincl U) /= [b [-> ]]; rewrite /val_uincl /= => ->.
  + case: v1 v2 U Aeq => //;last by move=> [] //=???;case:ifP.
    by move=> s1 n1 a1 []//= s2 n2 a2 [? [??]];subst => /Varr_inj1 <-. 
  by move=> /(of_val_uincl U) /=  /= [w [-> ]] => /andP [_ /eqP ->];rewrite zero_extend_u.
Qed.

Lemma truncate_value_uincl_a ty v1 v2 v1' : 
  value_uincl_a v1 v2 -> 
  truncate_val ty v1 = ok v1' ->
  truncate_val ty v2 = ok v1'.
Proof.
  by rewrite /truncate_val => U;t_xrbindP => v /(of_val_uincl_a U) -> /= ->.
Qed.

Definition eqok (e1 e2:pexpr) st := 
  forall v, sem_pexpr gd st e1 = ok v -> 
    exists v', sem_pexpr gd st e2 = ok v' /\ value_uincl_a v v'.

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

Lemma sint_of_wordP sz e : Papp1 (Oint_of_word sz) e =E sint_of_word sz e.
Proof.
  rewrite /sint_of_word => s.
  case: (is_wconst _ _) (@is_wconstP gd s sz e); last by move => _ ?; eauto.
  move => w /(_ _ erefl); t_xrbindP => v ok_v ok_w v'.
  rewrite /= /sem_sop1 /= ok_v /= ok_w => - [<-{v'}]; eauto.
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
Proof. case: o => [?|?|??|??||?|[|?]]; eauto using sint_of_wordP, snot_boolP, snot_wP, sneg_intP, sneg_wP. Qed.

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

Lemma value_uincl_a_zero_ext (sz sz' : wsize) (w' : word sz'):
  (sz ≤ sz')%CMP → value_uincl_a (Vword (zero_extend sz w')) (Vword w').
Proof. by move=> hle;split;first by apply value_uincl_zero_ext. Qed.

Local Hint Resolve value_uincl_a_zero_ext.

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

Lemma s_op2P o e1 e2 : Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case: o;eauto using sandP, sorP, saddP, smulP, ssubP, sdivP, smodP, 
                      s_eqP, sneqP, sltP, sleP, sgtP, sgeP,
                      slandP, slorP, slxorP, slslP, slsrP, sasrP.
Qed.

Definition vconst c :=
  match c with
  | Cint z => Vint z
  | Cword sz z => Vword z
  end.

Definition valid_cpm (vm: vmap)  (m:cpm) := 
  forall x n, Mvar.get m x = Some n -> get_var vm x = ok (vconst n).

Lemma const_prop_eP (e:pexpr) s (m:cpm):  
  valid_cpm (evm s) m ->
  e =[s] const_prop_e m e.
Proof.
  move=> Hvalid;rewrite /eqok.
  elim: e=> [z | b | sz n | x | g | x e He | sz x e He | o e He | o e1 He1 e2 He2 | op es ih | e He e1 He1 e2 He2] v /=;
  try (intros; clarify; eauto; fail).
  + move: (Hvalid x); case: Mvar.get => [n /(_ _ erefl) |_ /= -> ]; last by eauto.
    by case: n => [ n | sz w ] /= -> [<-]; rewrite /sem_sop1 /= ?wrepr_unsigned; eauto.
  + apply:on_arr_varP; rewrite /on_arr_var => ? n t ? -> /=.
    t_xrbindP => z w /(He _) [v'] [->] [/value_uincl_int h A] /h {h} [??]; subst.
    move => a ha ?; subst; rewrite /= ha.
    by eexists; (split; first reflexivity) => /=.
  + t_xrbindP => ? ? -> /= -> ? ? /He [v'] [->] [/value_uincl_word h A] /h {h} /=.
    rewrite /to_pointer => -> /= ? -> <- /=.
    by eexists; ( split; first reflexivity ) => /=.
  + t_xrbindP => v' /He [w] [hw [hvw A]] h; apply /s_op1P.
    rewrite /= hw /=.
    by apply: vuincl_sem_sop1 h.
  + t_xrbindP => v1 /He1 [w1] [hw1 [hvw1 A1]] v2 /He2 [w2] [hw2 [hvw2 A2]] h; apply/s_op2P.
    rewrite /= hw1 hw2 /=.
    by apply: vuincl_sem_sop2 h.
  + done. (* TODO: nary *)
  t_xrbindP => b vb /He [wb] [hwb] [/value_uincl_bool h A]/h {h} [??]; subst.
  move => v1 /He1 [w1] [hw1 [hvw1 A1]] v2 /He2 [w2] [hw2 [hvw2 A2]].
  case: ifP => // h; case: andP => // - [] /(value_uincl_is_defined hvw1) hd1 /(value_uincl_is_defined hvw2) hd2 [<-].
  rewrite /s_if. case: is_boolP hwb => [ [] | ] /=.
  + by case => <-;exists w1.
  + by case => <-;exists w2.
  move => p -> /=; rewrite hw1 hw2 /=.
  rewrite -(value_uincl_vundef_type_eq hvw1) -(value_uincl_vundef_type_eq hvw2) h hd1 hd2 /=.
  eexists;split;first reflexivity.
  by case: (b).
Qed.

Definition eqoks e1 e2 st :=
  ∀ vs, sem_pexprs gd st e1 = ok vs → ∃ vs', sem_pexprs gd st e2 = ok vs' ∧ List.Forall2 value_uincl_a vs vs'.

Lemma const_prop_esP es s m :
  valid_cpm (evm s) m →
  eqoks es (map (const_prop_e m) es) s.
Proof.
move => hv; elim: es.
+ by move => ? [<-]; exists [::].
move => e es ih ?; rewrite /sem_pexprs /=.
apply: rbindP => v /(const_prop_eP hv) [v'] [->] hu.
apply: rbindP => vs /ih{ih}; rewrite -/(sem_pexprs gd s _) => - [vs'] [->] hrec [<-] /=; eauto.
Qed.

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

Lemma add_cpmP s1 s1' m x e tag ty v v' :
  sem_pexpr gd s1 e = ok v ->
  truncate_val ty v = ok v' ->
  write_lval gd x v' s1 = ok s1' ->
  valid_cpm (evm s1') m -> 
  valid_cpm (evm s1') (add_cpm m x tag ty e).
Proof.
  rewrite /add_cpm;case: x => [xi | x | x | x] //= He.
  case: tag => //.
  case: e He => // [ n | [] // sz [] //= q ] [<-].
  + case/truncate_val_int => [??]; subst.
    case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
    have := Hv z n0.
    case: ({| vtype := sint; vname := xn |} =P z).
    + move=> <- /=;rewrite Mvar.setP_eq=> ? -[] <-;by rewrite /get_var Fv.setP_eq.
    by move=> /eqP Hneq;rewrite Mvar.setP_neq.
  case/truncate_val_word => szw [] -> hle -> /=.
  rewrite zero_extend_wrepr //.
  case: x => -[] [] //= szx xn vi; apply: rbindP => vm.
  apply: set_varP => //= w' [<-] <- [<-] /= Hv z /= n.
  have := Hv z n.
  case: ({| vtype := sword szx; vname := xn |} =P z).
  + move=> <- /=. rewrite Mvar.setP_eq=> ? -[] <-; rewrite /get_var Fv.setP_eq /=.
    f_equal.
    by case: Sumbool.sumbool_of_bool => /= ->.
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
  case:x => [ii t | x | sz x p | x p] /= Hv.
  + by move=> H; have [??]:= write_noneP H; subst s2.
  + by move=> H;split=>//;apply: remove_cpm1P H Hv.
  + apply: rbindP => z Hz;rewrite Hz /=.
    apply: rbindP => z'.
    apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) [] z3 [] -> /= [/value_uincl_word h _] /h {h} ->.
    by apply: rbindP => w -> /=;apply: rbindP => m' -> [<-].
  apply: on_arr_varP;rewrite /on_arr_var => ? n t Htx -> /=.
  apply: rbindP => z;apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) [] z3 [] ->.
  move => [/value_uincl_int h _] /h {h} [] ??; subst.
  apply: rbindP => w -> /=;apply: rbindP => t' -> /=.
  apply: rbindP => vm Hvm [<-];rewrite Hvm;split=>//=.
  have H : write_var x (Varr t') s1 = ok (Estate (emem s1) vm) by rewrite /write_var Hvm.
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
  + by move=> ?? ->.
  + by move=> ??? ->.
  + by move=> ?? ->.
  + by move=> ?? -> ? ->.
  + move => op es h; f_equal.
    elim: es h => // e es ih rec /=; f_equal.
    - by apply: rec; rewrite in_cons eqxx.
    by apply: ih => e' he'; apply: rec; rewrite in_cons he' orbT.
  by move=> ? -> ? -> ? ->.
Qed.

Instance const_prop_rv_m : 
  Proper (@Mvar_eq const_v ==> eq ==> RelationPairs.RelProd (@Mvar_eq const_v) eq) const_prop_rv.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => [ v | v | sz v p | v p] //=;rewrite Hm.
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

  Local Lemma Wwhile c e c': Pc c -> Pc c' -> Pr (Cwhile c e c').
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

End PROPER.

Lemma const_prop_i_m : 
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) const_prop_i. 
Proof.
  move=> m1 m2 Hm i1 i2 <-.
  apply : (instr_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_i_r_m : 
  Proper (@Mvar_eq const_v ==> eq ==> eq ==> @Mvarc_eq const_v) const_prop_ir. 
Proof.
  move=> m1 m2 Hm ii1 ii2 <- i1 i2 <-.
  apply : (instr_r_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_m : 
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) (const_prop const_prop_i). 
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

  Variable p:prog.
  Notation gd := (p_globs p).

  Let p' := const_prop_prog p.

  Let Pi s (i:instr) s':= 
    forall m, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop_i m i).1 /\
      sem p' s (const_prop_i m i).2 s'.

  Let Pi_r s (i:instr_r) s':= 
    forall m ii, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop_ir m ii i).1 /\
      sem p' s (const_prop_ir m ii i).2 s'.

  Let Pc s (c:cmd) s':= 
    forall m, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop const_prop_i m c).1 /\
      sem p' s (const_prop const_prop_i m c).2 s'.

  Let Pfor (i:var_i) vs s c s' :=
    forall m, 
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s.(evm) m ->
      sem_for p' i vs s (const_prop const_prop_i m c).2 s'.

  Let Pfun m fn vargs m' vres :=
    forall vargs', List.Forall2 value_uincl_a vargs vargs' ->
    sem_call p' m fn vargs' m' vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s m /= ?;split=>//; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc m /Hi [] /=.
    case: const_prop_i => m' i' /Hc [].
    case: const_prop => m'' c' /= Hm'' Hc' Hi';split=> //.
    by apply: sem_app Hi' Hc'.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi m /(Hi _ ii). Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' He htr Hw m ii /= Hm.
    have [v1 [H U]] := const_prop_eP Hm He.
    have :=truncate_value_uincl_a U htr. 
    have [] := const_prop_rvP Hm Hw.
    case: const_prop_rv => m' x' /= Hm' Hw';split.
    + by eapply add_cpmP;eauto.
    by apply sem_seq1;constructor;econstructor;eauto.
  Qed.

  Definition not_sarr t := if t is sarr _ _ then false else true.

  Lemma app_sopn_uincl_a ts op vs vs' vres:
    all not_sarr ts -> 
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

  Lemma exec_sopn_uincl_a o vs vs' vres : 
    exec_sopn o vs = ok vres ->
    List.Forall2 value_uincl_a vs vs' ->
    exec_sopn o vs' = ok vres.
  Proof.
    case: o; try by
        try (refine (λ _ : velem, _));
        do 2 try (refine (λ _ : wsize, _));
        apply: app_sopn_uincl_a.
    move=> w /=;case: vs => //= v1 [// | v2 [// | v3 [|//]]] H.
    case/List_Forall2_inv_l => v1' [vs''] [->] {vs'} [hv1] /List_Forall2_inv_l [v2'] [vs'] [->] {vs''} [hv2] /List_Forall2_inv_l [v3'] [vs''] [->] {vs'} [hv3] /List_Forall2_inv_l -> {vs''}.
    move: H hv1;t_xrbindP => _ -> /= b /value_uincl_bool h H [] /h {h} [??] _; subst => /=.
    case: b H; t_xrbindP => w'.
    + by case: hv2 => /value_uincl_word h _ /h -> <-.
    by case: hv3 => /value_uincl_word h _ /h -> <-.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H m ii Hm; apply: rbindP H => vs.
    apply: rbindP => ves Hes Ho Hw;move: (Hes) (Hw).
    move=> /(const_prop_esP Hm) [vs' [Hes' Us]] /(const_prop_rvsP Hm) [] /=.
    case: const_prop_rvs => m' rvs' /= ??;split=>//.
    apply sem_seq1; do 2 constructor.
    by rewrite /sem_sopn Hes' /= (exec_sopn_uincl_a Ho Us).
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 He _ Hc1 m ii Hm.
    have  [v' [{He} He []]] /= := const_prop_eP Hm He.
    case: v' He => //= ? He ? _;subst.
    case : is_boolP He => [b [] ->| {e} e He];first by apply Hc1.
    case: (Hc1 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;left.
    by apply sem_seq1; do 2 constructor=> //;rewrite He.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 He _ Hc2 m ii Hm.
    have  [v' [{He} He []]] /= := const_prop_eP Hm He.
    case: v' He => //= ? He ? _;subst.
    case: is_boolP He => [b [] -> | {e} e He];first by apply Hc2.
    case: (Hc2 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;right.
    by apply sem_seq1; constructor;apply Eif_false=> //;rewrite He.
  Qed.

  (* TODO: move this *)    
  Lemma sem_seq1_iff (P : prog) (i : instr) (s1 s2 : estate):
     sem_I P s1 i s2 <-> sem P s1 [:: i] s2.
  Proof.
    split; first by apply sem_seq1.
    by case/semE => ? [?] /semE ->.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 c e c' Hc1 Hc He Hc1' Hc' Hw1 Hw m ii Hm /=.
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
    have /= : Mvarc_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile c e c'))) c)
               (m'', c0).
    + by have := const_prop_m H1 (refl_equal c); rewrite Heq1.
    case: const_prop  => m2'' c2 [].
    rewrite /RelationPairs.RelCompFun /= => Hm2'' ->.
    have /= : Mvarc_eq (const_prop const_prop_i m2'' c') (m_, c0').
    + by have := const_prop_m Hm2'' (refl_equal c'); rewrite Heq2.
    case: const_prop  => ? c2' [].
    rewrite /RelationPairs.RelCompFun /= => _ -> -[Hs4 Hsem];split.
    by apply (valid_cpm_m (refl_equal (evm s4)) Hm2'').
    move: Hsem.
    have -> : const_prop_e m2'' e = const_prop_e m'' e.
    + by rewrite Hm2''.
    have H :  forall e0, 
      sem_pexpr gd s2 e0 = ok (Vbool true) ->
      sem p' s3 [:: MkI ii (Cwhile c0 e0 c0')] s4 ->
      sem p' s1 [:: MkI ii (Cwhile c0 e0 c0')] s4.
    + move=> e0 He0 /sem_seq1_iff /sem_IE Hsw;apply:sem_seq1;constructor.
      by apply: (Ewhile_true Hc0 _ Hc0' Hsw).
    have [v' [Hv' []/=]]:= const_prop_eP Hm'' He.
    case: v' Hv' => // ? Hv' ? _;subst.
    by case:is_boolP Hv' => [? [->]| e0 He0]; apply H.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
    move=> s1 s2 c e c' Hc1 Hc He m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c0] /=.
    case Heq2: const_prop => [m_ c0'] /=.
    have eq1_1 : evm s1 = evm s1 [\ww] by done.
    have /Hc:= valid_cpm_rm eq1_1 Hm;rewrite -/m' Heq1 /= => -[Hm'' Hc0];split => //.
    have [v' [Hv' []/=]]:= const_prop_eP Hm'' He.
    case: v' Hv' => // ? Hv' ? _;subst.
    case:is_boolP Hv' => [ ?[->] //| e0 He0].
    by apply: sem_seq1;constructor;apply: Ewhile_false => //;rewrite He0.
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
    apply sem_seq1;constructor;econstructor;eauto.
    + by have [v' [h [/=]]] := const_prop_eP Hm Hlo;case: v' h => //= ?? ->.
    by have [v' [h [/=]]] := const_prop_eP Hm Hhi;case: v' h => //= ?? ->.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c m Hm;constructor. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move => s1 s1' s2 s3 i w ws c Hw Hsemc Hc Hsemf Hf m Heqm Hm.
    have Hm' : valid_cpm (evm s1') m.
    + have Hmi : Mvar_eq m (Mvar.remove m i).
      + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //]. 
        rewrite Heqm;move: (remove_cpm_spec m (Sv.union (Sv.singleton i) (write_c c)) i).
        by case: Mvar.get => // a [];SvD.fsetdec.
      have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
      by apply: remove_cpm1P Hw Hm.
    have [_ Hc']:= Hc _ Hm'.        
    have /(Hf _ Heqm) : valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec. 
    by apply: EForOne Hc'.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfun Hvs m ii' Hm.
    have [vargs' [Hargs' Hall]] := const_prop_esP Hm Hargs.
    have /(_ _ Hm) [] /=:= const_prop_rvsP _ Hvs.
    case: const_prop_rvs => m' rvs' /= ??;split=>//.
    by apply sem_seq1;constructor;econstructor;eauto.
  Qed.

  Lemma mapM2_truncate_val_uincl_a ts v1 v2 v1' : 
    List.Forall2 value_uincl_a v1 v2 →
    mapM2 ErrType truncate_val ts v1 = ok v1' → 
    mapM2 ErrType truncate_val ts v2 = ok v1'.
  Proof.
    move=> hall;elim: hall ts v1' => {v1 v2} [ | v1 v2 vs1 vs2 hv hall hrec];case => //= t ts v1'.
    by t_xrbindP => v' /(truncate_value_uincl_a hv) -> vs' /hrec -> /= <-.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres'.
    case: f=> fi ftin fparams fc ftout fres /= Hget Hargs Hw _ Hc Hres Hfull.
    have := (@get_map_prog const_prop_fun p fn);rewrite Hget /=.
    have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
    move=> /Hc [];case: const_prop;econstructor;eauto => /=.
    by apply: mapM2_truncate_val_uincl_a Hargs. 
  Qed.

  Lemma const_prop_callP f mem mem' va vr:
    sem_call p mem f va mem' vr ->
    sem_call p' mem f va mem' vr.
  Proof.
    move=> /(@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) h.
    apply h;apply List_Forall2_refl;apply: value_uincl_a_refl.
  Qed.

End PROOF.
