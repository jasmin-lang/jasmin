(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
Require Import psem compiler_util.
Require Export constant_prop it_sems_core hoare_logic relational_logic.

Import Utf8 ZArith Morphisms Classes.RelationClasses.
Import RelationPairs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Local Notation cpm := (Mvar.t const_v).

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {wsw:WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Section GLOB_DEFS.

Context (wdb : bool) (gd: glob_decls).

Definition eqok_w (e1 e2:pexpr) st :=
  forall v, sem_pexpr wdb gd st e1 = ok v -> sem_pexpr wdb gd st e2 = ok v.

Definition eqok (e1 e2:pexpr) st :=
  forall v, sem_pexpr wdb gd st e1 = ok v ->
    exists v', sem_pexpr wdb gd st e2 = ok v' /\ value_uincl v v'.

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

(* -------------------------------------------------------- *)

Lemma snotP e : Papp1 Onot e =E snot e.
Proof.
  apply: eeq_weaken.
  elim: e=> //=;try auto; first by move=> ???.
  + case; auto.
    move=> e _ rho v /=; t_xrbindP => ?? -> /sem_sop1I /= [b] /to_boolI -> -> /sem_sop1I /= [b'] [<-] ->.
    by rewrite negbK.
  + case; auto => e1 hrec1 e2 hrec2 rho v /=;
    t_xrbindP => ? ? he1 ? he2 /sem_sop2I /= [b1 [b2 [b]]] [] /to_boolI ? /to_boolI
      ? [] ?? /sem_sop1I /= [?] /to_boolI h ?; subst; case: h => ?; subst;
      have := hrec1 rho _; have := hrec2 rho _;
      rewrite /= he1 he2 /sem_sop1 /= => /(_ _ erefl) -> /(_ _ erefl) -> /=; rewrite /sem_sop2 /=.
    + by rewrite -negb_and.
    by rewrite negb_or.
  move=> t e _ e1 hrec1 e2 hrec2 rho v /=.
  t_xrbindP => v' be ve he /to_boolI ?; subst.
  move=> tve1 ve1 he1 hte1 tve2 ve2 he2 hte2 ?; subst v'.
  move=> /sem_sop1I /= [b] /to_boolI h ?; subst.
  have := hrec1 rho _; have := hrec2 rho _;
  rewrite he /= he1 he2 /= /sem_sop1 /=.
  have [b1 [b2 [??]]]: exists (b1 b2: bool), tve1 = b1 /\ tve2 = b2.
  + case: (be) h => ?; subst.
    + have [??]:= truncate_valI hte1; subst.
      by move: hte2; rewrite /truncate_val /=; t_xrbindP => ? /to_boolI ??; subst; eauto.
    have [??]:= truncate_valI hte2; subst.
    by move: hte1; rewrite /truncate_val /=; t_xrbindP => ? /to_boolI ??; subst; eauto.
  subst.
  have [??]:= truncate_valI hte1; have [??]:= truncate_valI hte2; subst => /=.
  move=> /(_ _ erefl) -> /(_ _ erefl) -> /=.
  by case: (be) h => -[->].
Qed.

Lemma sneg_intP e : Papp1 (Oneg Op_int) e =E sneg_int e.
Proof.
apply: eeq_weaken; case: e => // [ z s v [] <- // | [] ] // [] // e s v /=; t_xrbindP => ? ? -> /=.
rewrite /sem_sop1; t_xrbindP => ? /to_intI -> <- /= ? [<-] <-.
by rewrite Z.opp_involutive.
Qed.

Lemma e2boolP e b :
   e2bool e = ok b -> e = Pbool b.
Proof. by case: e => //= ? [->]. Qed.

Lemma e2intP e z :
   e2int e = ok z -> e = Pconst z.
Proof. by case: e => //= ? [->]. Qed.

Lemma of_exprP rho t e v :
  of_expr t e = ok v ->
  Let x := sem_pexpr wdb gd rho e in of_val t x = ok v.
Proof.
  case: t v => //= [b /e2boolP -> | z /e2intP -> | w] // v.
  by rewrite /e2word; case heq : is_wconst => [w' | ] // [<-]; apply is_wconstP.
Qed.

Lemma to_exprP rho t (v:sem_t t) e : to_expr v = ok e -> sem_pexpr wdb gd rho e = ok (to_val v).
Proof.
  case: t v => //= [b | z | ws w] [<-] //=.
  by rewrite /sem_sop1 /= wrepr_unsigned.
Qed.

Lemma ssem_sop1P o e : Papp1 o e =E ssem_sop1 o e.
Proof.
  rewrite /ssem_sop1.
  case heq : of_expr => [ v | ] //=.
  apply: eeq_weaken => rho v' /[dup]h1 /=.
  rewrite /sem_sop1 -Let_Let (of_exprP rho heq) /= => -[?]; subst v'.
  by case heq' : to_expr => [e' | //]; apply to_exprP.
Qed.

Lemma s_op1P o e : Papp1 o e =E s_op1 o e.
Proof.
  case: o => [?|?|??|??||?|[|?]];
  eauto using snotP, sneg_intP, ssem_sop1P.
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
    apply: rbindP => z2 /to_intI ? /=;subst v2=> [<-].
    by case: eqP => [-> // | /= _];rewrite Hv2.
  apply: rbindP => v1 Hv1;rewrite /sem_sop2 /=.
  apply: rbindP => z1 /to_intI ? /=;subst v1=> [<-].
  by case: eqP => [-> // | /= _];rewrite Hv1 //= Z.add_0_r.
Qed.

Lemma sadd_wP sz e1 e2 : Papp2 (Oadd (Op_w sz)) e1 e2 =E sadd_w sz e1 e2.
Proof.
rewrite /sadd_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] //.
+ move => s v /=; rewrite /sem_sop2 /sem_sop1 /=.
  have! := (is_wconstP wdb gd s h2).
  have! := (is_wconstP wdb gd s h1).
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
+ case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
  have! := (is_wconstP wdb gd s h1).
  t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
  case: (to_wordI k6) => sz' [w' [? /truncate_word_uincl ?]]; subst.
  by rewrite GRing.add0r k4;eauto.
case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
have! := (is_wconstP wdb gd s h2).
t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
case: (to_wordI k5) => sz' [w' [? /truncate_word_uincl ?]]; subst.
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
  apply: rbindP => z1 /to_intI ? /=;subst v1=> [<-].
  by case: eqP => [-> | /= _];rewrite Hv1 ?Z.sub_0_r.
Qed.

Lemma ssub_wP sz e1 e2 : Papp2 (Osub (Op_w sz)) e1 e2 =E ssub_w sz e1 e2.
Proof.
rewrite /ssub_w.
case h1: (is_wconst sz e1) => [ n1 | ];
case h2: (is_wconst sz e2) => [ n2 | ] //.
+ move => s v /=; rewrite /sem_sop2 /sem_sop1 /=.
  have! := (is_wconstP wdb gd s h2).
  have! := (is_wconstP wdb gd s h1).
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
case: eqP => // hz s v /=; rewrite /sem_sop2 /=.
have! := (is_wconstP wdb gd s h2).
t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 <-; clarify.
case: (to_wordI k5) => sz' [w' [? /truncate_word_uincl ?]]; subst.
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
    apply: rbindP => z2 /to_intI ?;subst v2.
    case:eqP => [-> //|_]; case:eqP => [-> | _ /=];last by rewrite Hv2.
    by rewrite Z.mul_1_l => -[<-].
  apply: rbindP => v1 Hv1. rewrite /sem_sop2 /=.
  apply: rbindP => z1 /to_intI ?;subst v1.
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
  have! := (is_wconstP wdb gd s h2).
  have! := (is_wconstP wdb gd s h1).
  by t_xrbindP => *; clarify; rewrite wrepr_unsigned;eauto.
+ case: eqP => hn1; [| case: eqP => hn2] => s v /=; rewrite /sem_sop2 /sem_sop1 /=;
  have! := (is_wconstP wdb gd s h1);
  t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 ?; clarify.
  - rewrite wrepr_unsigned GRing.mul0r;eauto.
  - case: (to_wordI k6) => {k6} sz' [w] [? /truncate_word_uincl]; subst.
    by rewrite k4 GRing.mul1r; eauto.
  by rewrite k4 /= k6 /= wrepr_unsigned truncate_word_u /=;eexists;split;eauto => /=.
case: eqP => hn1; [| case: eqP => hn2] => s v /=; rewrite /sem_sop2 /sem_sop1 /=;
have! := (is_wconstP wdb gd s h2);
t_xrbindP => ? k1 k2 ? k3 ? k4 ? k5 ? k6 ?; clarify.
- by rewrite wrepr_unsigned GRing.mulr0;eauto.
- case: (to_wordI k5) => {k5} sz' [w] [? /truncate_word_uincl ?]; subst.
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
  t_xrbindP => v1 k1 v2 k2 w1' /to_wordI [sz1 [w1 [? hle1]]]
                  w2' /to_wordI [sz2 [w2 [? hle2]]] ? /= [] ? ?;subst.
  eexists; split; first reflexivity.
  have! := (is_wconstP wdb gd s h1); rewrite k1 /= hle1 => -[?]; subst.
  have! := (is_wconstP wdb gd s h2); rewrite k2 /= hle2 => -[?]; subst.
  done.
Qed.

Lemma sbeqP e1 e2 : Papp2 Obeq e1 e2 =E sbeq e1 e2.
Proof.
  rewrite /sbeq; apply eeq_weaken.
  case: (is_boolP e1) => [b1 | {e1}e1]; case: (is_boolP e2) => [b2 | {e2} e2] // rho v.
  + by rewrite /= /sem_sop2 /= => -[<-].
  + rewrite /= /sem_sop2 /=; t_xrbindP => v2 he2 b2 /to_boolI ??; subst; rewrite eq_sym.
    case: b1; first by rewrite eqb_id.
    rewrite eqbF_neg.
    have []:= @snotP e2 rho (~~b2).
    + by rewrite /= he2.
    by move=> v [] -> /value_uinclE ->.
  rewrite /= /sem_sop2 /=; t_xrbindP => v1 he1 b1 /to_boolI ??; subst.
  case: b2; first by rewrite eqb_id.
  rewrite eqbF_neg.
  have []:= @snotP e1 rho (~~b1).
  + by rewrite /= he1.
  by move=> v [] -> /value_uinclE ->.
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
  t_xrbindP => v1 k1 v2 k2 w1' /to_wordI [sz1 [w1 [? hle1]]]
                  w2' /to_wordI [sz2 [w2 [? hle2]]] ? /= [] ? ?;subst.
  eexists; split; first reflexivity.
  have! := (is_wconstP wdb gd s h1); rewrite k1 /= hle1 => -[?]; subst.
  have! := (is_wconstP wdb gd s h2); rewrite k2 /= hle2 => -[?]; subst.
  done.
Qed.

Lemma is_cmp_constP s ty e z :
  is_cmp_const ty e = Some z →
  match ty with
  | Cmp_int => e = Pconst z
  | Cmp_w sg sz =>
    exists2 x,
    sem_pexpr wdb gd s e = ok x &
    exists2 w,
    to_word sz x = ok w &
    match sg with
    | Signed => wsigned w = z
    | Unsigned => wunsigned w = z
    end
  end.
Proof.
  case: ty => /=.
  - by case: is_constP => // ? /Some_inj <-.
  move => sg sz /oseq.obindI [] w [] /(is_wconstP wdb gd s).
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
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= word_ssrZ.ltzE.
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
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= word_ssrZ.lezE.
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
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= Z.gtb_ltb word_ssrZ.ltzE.
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
    rewrite /= ok_v1 ok_v2 /= /sem_sop2 /= ok_w1 ok_w2 /= Z.geb_leb word_ssrZ.lezE.
Qed.

Lemma ssem_sop2P o e1 e2 : Papp2 o e1 e2 =E ssem_sop2 o e1 e2.
Proof.
  rewrite /ssem_sop2.
  case heq1 : (of_expr _ e1) => [ v1 | ] //=.
  case heq2 : (of_expr _ e2) => [ v2 | ] //=.
  apply: eeq_weaken => rho v' /[dup]h1 /=.
  rewrite /sem_sop2.
  move: (of_exprP rho heq1) (of_exprP rho heq2).
  t_xrbindP => ? -> he1 ? -> he2 ? [<-] ? [<-]; rewrite he1 he2 => ?[<-] ?[<-] ? -> ? /=; subst v'.
  by case heq' : to_expr => [e' | //]; apply to_exprP.
Qed.

Lemma s_op2P o e1 e2 : Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case: o;eauto using sandP, sorP, saddP, smulP, ssubP, sbeqP,
                      s_eqP, sneqP, sltP, sleP, sgtP, sgeP, ssem_sop2P.
Qed.

Lemma app_sopnP T0 ts o es x s :
  @app_sopn T0 ts o es = ok x ->
  sem_pexprs wdb gd s es >>= values.app_sopn ts o = ok x.
Proof.
  elim: ts es o => /= [ | t ts ih ].
  + by case=> // _ -> [<-].
  case=> //= e es ty.
  t_xrbindP=> z hz /ih{ih}.
  have := of_exprP s hz.
  t_xrbindP=> v -> /= hval vs -> /=.
  by rewrite hval.
Qed.

Lemma s_opNP op s es :
  sem_pexpr wdb gd s (s_opN op es) = sem_pexpr wdb gd s (PappN op es).
Proof.

Opaque app_sopn values.app_sopn.
  rewrite /s_opN.
  case h: app_sopn => [r | //].
  case: op r h => [sz' pe | c] /=.

  + move=> w h.
    rewrite /sem_sop1 /= wrepr_unsigned /sem_opN /=.
    by rewrite -Let_Let (app_sopnP _ h).

  move=> b h.
  rewrite /sem_opN /=.
  by rewrite -Let_Let (app_sopnP s h).
Transparent app_sopn values.app_sopn.

Qed.

Definition vconst c :=
  match c with
  | Cbool b => Vbool b
  | Cint z => Vint z
  | Cword sz z => Vword z
  end.

Definition valid_cpm (vm: Vm.t)  (m:cpm) :=
  forall x n, Mvar.get m x = Some n -> vm.[x] = vconst n.

Lemma valid_cpm_empty vm :
  valid_cpm vm empty_cpm.
Proof. move=> x n. by rewrite Mvar.get0. Qed.

Definition eqoks e1 e2 st :=
  ∀ vs, sem_pexprs wdb gd st e1 = ok vs → exists2 vs', sem_pexprs wdb gd st e2 = ok vs' & List.Forall2 value_uincl vs vs'.

Definition valid_globs (globs: globals) : Prop :=
  if globs is Some f then
    ∀ x gv v, f x = Some gv → get_global gd x = ok v → v = gv2val gv
  else True.

Section CONST_PROP_EP.
  Context (globs: globals) (s:estate) m (Hvalid: valid_cpm (evm s) m) (Gvalid: valid_globs globs).
  Let P e : Prop := e =[s] const_prop_e globs m e.
  Let Q es : Prop := eqoks es (map (const_prop_e globs m) es) s.

  Lemma const_prop_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; subst P Q; rewrite /eqok; split => /=;
    try (intros; clarify; eauto; fail).
    - by move => ? [<-]; exists [::].
    - move => e rec es ih ?; rewrite /sem_pexprs /=.
      apply: rbindP => v /rec [v'] [->] hu.
      by apply: rbindP => vs /ih{ih}; rewrite -/(sem_pexprs wdb gd s _) => - [vs'] -> hrec [<-] /=; eauto.
    - move => [x []] v; rewrite /= /get_gvar /=; last first.
      + case: globs Gvalid; last by eauto.
        move => f /(_ x).
        case ok_v: get_global => [ v' | ] // + /ok_inj ?; subst v'.
        case: f; last by rewrite /= /get_gvar /= ok_v; eauto.
        move => gv /(_ _ _ erefl erefl) ?; subst v.
        case: gv ok_v; last by rewrite /= /get_gvar /= => ?? ->; eexists.
        move => ???; eexists; split; first reflexivity.
        by rewrite /= wrepr_unsigned.
      move: Hvalid => /(_ x).
      case: Mvar.get => [n /(_ _ erefl)| _ /= ]; last by rewrite /= /get_gvar /=;eauto.
      move=> hx /get_varP; rewrite hx => -[-> _ _] {hx}.
      by case: n => [ b | n | sz w ]; rewrite /sem_sop1 /= ?wrepr_unsigned;
           eexists;(split;first reflexivity) => //=; rewrite wrepr_unsigned.
    - move => al aa sz x e He v.
      apply: on_arr_gvarP => n t wt ok_x.
      t_xrbindP => z w /(He _) {He} [v'] [] ok_v' /[swap] /to_intI ? /value_uinclE; subst => ?; subst.
      move => a ha ?; subst.
      have default : ∃ v' : value, sem_pexpr wdb gd s (Pget al aa sz x (const_prop_e globs m e)) = ok v' ∧ value_uincl (Vword a) v'.
      + by rewrite /= /on_arr_var ok_x /= ok_v' /= ha /=; eexists; split; [ reflexivity | simpl ].
      case x_glob: is_glob; last exact: default.
      case: globs default Gvalid ok_v'; last by [].
      move => f + /(_ x.(gv)).
      case: (f _); last by [].
      case; first by [].
      move => len arr.
      rewrite (get_gvar_glob _ _ _ x_glob) in ok_x.
      case: (const_prop_e _) => // i _ /(_ _ _ erefl ok_x) /= /Varr_inj[] ??; subst => /= /ok_inj[] ?; subst.
      rewrite ha /=.
      eexists; split; first reflexivity.
      by rewrite /= wrepr_unsigned.
    - move => aa sz len x e He v.
      apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
      t_xrbindP => z w /(He _) [v'] [->] /[swap] /to_intI -> /value_uinclE ->.
      move => a ha ?; subst; rewrite /= ha.
      by eexists; (split; first reflexivity) => /=.
    - move => al sz x e He v.
      t_xrbindP => ? ? -> /= -> ? ? /He [v'] [->] /[swap]
        /to_wordI[? [? [-> /word_uincl_truncate h]]]
        /value_uinclE[? [? [-> /h{h}h]]] ? h' <- /=.
      rewrite h /= h' /=.
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
      t_xrbindP => vs /ih{ih} [] vs' ih /vuincl_sem_opN h/h{h} ok_v.
      by rewrite s_opNP /= -/(sem_pexprs _ _ _) ih /= ok_v; eauto.
    move => t e He e1 He1 e2 He2 v.
    t_xrbindP => b ve /He/= [] ve' [] hse /[swap] /to_boolI -> /value_uinclE ?; subst.
    move=> ve1 vte1 /He1 []ve1' [] hse1 hue1 /(value_uincl_truncate hue1) [] ? /[dup] ht1 /truncate_value_uincl ht1' hu1.
    move=> ve2 vte2 /He2 []ve2' [] hse2 hue2 /(value_uincl_truncate hue2) [] ? /[dup] ht2 /truncate_value_uincl ht2' hu2 <-.
    rewrite /s_if; case: is_boolP hse; first by move=> [][<-] /=;eexists;split;eauto using value_uincl_trans.
    move=> /= p -> /=;rewrite hse1 hse2 /= ht1 ht2 /=;eexists;split;eauto.
    by case:(b).
  Qed.

End CONST_PROP_EP.

Definition const_prop_eP globs e s m h g :=
  (@const_prop_e_esP globs s m h g).1 e.

Definition const_prop_esP globs es s m h g :=
  (@const_prop_e_esP globs s m h g).2 es.

Definition empty_const_prop_eP e s :=
  const_prop_eP (e := e) (s := s) (valid_cpm_empty _) (I : valid_globs None).

Lemma remove_cpm1P x v m s1 s1' :
  write_var wdb x v s1 = ok s1' ->
  valid_cpm (evm s1) m ->
  valid_cpm (evm s1') (Mvar.remove m x).
Proof.
  move=> Hw Hv z n;rewrite Mvar.removeP;case: ifPn => //= hne /Hv.
  by move/write_varP: Hw => [-> _ _ /=]; rewrite Vm.setP_neq.
Qed.

Lemma add_cpmP s1 s1' m x e tag ty v1 v v' :
  wdb ->
  sem_pexpr wdb gd s1 e = ok v1 ->
  value_uincl v v1 ->
  truncate_val ty v = ok v' ->
  write_lval wdb gd x v' s1 = ok s1' ->
  valid_cpm (evm s1') m ->
  valid_cpm (evm s1') (add_cpm m x tag ty e).
Proof.
  rewrite /add_cpm;case: x => //= x hwdb He.
  case: tag => //.
  case: e He => // [n | b | [] // sz [] //= q ] [<-].
  + case: v => //= ?; last by move=> ?? /truncate_valE.
    move=> -> /truncate_valE [_ ->] hw hv z n0.
    rewrite Mvar.setP /=; case: eqP => [<- [<-]| hne]; last by apply hv.
    rewrite hwdb in hw *.
    by have [_ /vm_truncate_valE [hty ->] /get_varP [<-??]] := write_get_varP_eq hw.
  + case: v => //= ?;last by move=> ??/truncate_valE.
    move=> -> /truncate_valE [_ ->] hw hv z n0.
    rewrite Mvar.setP /=; case: eqP => [<- [<-]| hne]; last by apply hv.
    rewrite hwdb in hw *.
    by have [_ /vm_truncate_valE [hty ->] /get_varP [<-??]] := write_get_varP_eq hw.
  case: v => //= s ;last by move=> ??/truncate_valE.
  move=> w /andP[] Ule /eqP -> /truncate_valE [szw [ww [-> /truncate_wordP[hle ->] ->]]] /=.
  rewrite !(zero_extend_wrepr _ Ule, zero_extend_wrepr _ (cmp_le_trans hle Ule), zero_extend_wrepr _ hle).
  move=> hw hv z n.
  rewrite Mvar.setP /=; case: eqP => [<- [<-]| hne]; last by apply hv.
  rewrite hwdb in hw *.
  have [_ /vm_truncate_valE [ws' [-> _ -> /=]] /get_varP [<-]] := write_get_varP_eq hw.
  move => _ _.
  elim/cmp_minP: (cmp_min szw ws'); first by move => ->.
  move=> /[dup] /(@cmp_lt_le _ _ _ _ _) hle'.
  rewrite -cmp_nle_lt => /negbTE ->.
  by rewrite zero_extend_wrepr.
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

Lemma const_prop_rvP globs s1 s2 m x v:
  valid_cpm (evm s1) m ->
  valid_globs globs ->
  write_lval wdb gd x v s1 = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rv globs m x).1 /\
  write_lval wdb gd (const_prop_rv globs m x).2 v s1 = ok s2.
Proof.
  case:x => [ii t | x | al sz x p | al aa sz x p | aa sz len x p] /= Hv Gv; t_xrbindP.
  + by move=> H; have [??]:= write_noneP H; subst s2.
  + by move=> H;split=>//;apply: remove_cpm1P H Hv.
  + by move=> > -> /to_wordI [? [? [-> /= ->]]]
      > /(@const_prop_eP globs p _ _ Hv Gv) [? [-> ]]
      /[swap] /to_wordI [? [? [-> /word_uincl_truncate h]]]
      /value_uinclE [? [? [-> /h{h} /= ->]]] ? -> ? /= -> /= <-.
  all: by apply: on_arr_varP;rewrite /on_arr_var => n t Htx -> /=;
    t_xrbindP => > /(@const_prop_eP globs p _ _ Hv Gv) [? [-> ]] /[swap] /to_intI ->
      /value_uinclE -> ? -> ? /= -> /= h; split; first apply: remove_cpm1P h Hv.
Qed.

Lemma const_prop_rvsP globs s1 s2 m x v:
  valid_cpm (evm s1) m ->
  valid_globs globs ->
  write_lvals wdb gd s1 x v = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rvs globs m x).1 /\
  write_lvals wdb gd s1 (const_prop_rvs globs m x).2 v = ok s2.
Proof.
  elim: x v m s1 s2 => [ | x xs Hrec] [ | v vs] //= m s1 s2 Hm Gv.
  + by move=> [<-].
  apply: rbindP => s1' Hw Hws.
  have [/=]:= const_prop_rvP Hm Gv Hw.
  case Hx : const_prop_rv => [m1 rv'] /= Hm1 Hw'.
  have [/=]:= Hrec _ _ _ _ Hm1 Gv Hws.
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
  rho1 =[\ xs] rho2 ->
  valid_cpm rho1 m ->
  valid_cpm rho2 (remove_cpm m xs).
Proof.
  move=> Hrho Hval x nx /get_remove_cpm [] Hm Hin.
  rewrite -Hrho //; apply (Hval _ _ Hm).
Qed.

Lemma remove_cpmP s s' m x v:
  write_lval wdb gd x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv; apply: (valid_cpm_rm _ Hv);eapply vrvP;eauto. Qed.

End GLOB_DEFS.

#[local]
Instance const_prop_e_m :
  Proper (eq ==> @Mvar_eq const_v ==> eq ==> eq) const_prop_e.
Proof.
  move=> g _ <- m1 m2 Hm e e' <- {e'}.
  elim: e => //=.
  + by case => ? [] //; rewrite Hm.
  + by move=> ????? ->.
  + by move=> ????? ->.
  + by move=> ???? ->.
  + by move=> ?? ->.
  + by move=> ?? -> ? ->.
  + move => op es h; f_equal.
    elim: es h => // e es ih rec /=; f_equal.
    - by apply: rec; left.
    by apply: ih => e' he'; apply: rec; right.
  by move=> ?? -> ? -> ? ->.
Qed.

#[local]
Instance const_prop_rv_m :
  Proper (eq ==> @Mvar_eq const_v ==> eq ==> RelationPairs.RelProd (@Mvar_eq const_v) eq) const_prop_rv.
Proof.
  move=> g _ <- m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => [ v | v | al sz v p | al aa sz v p | aa sz len v p] //=;rewrite Hm.
Qed.

#[local]
Instance const_prop_rvs_m :
  Proper (eq ==> @Mvar_eq const_v ==> eq ==> RelationPairs.RelProd (@Mvar_eq const_v) eq) const_prop_rvs.
Proof.
  move=> g _ <- m1 m2 Hm rv rv' <- {rv'}.
  elim: rv m1 m2 Hm => //= rv rvs Hrec m1 m2 Hm.
  have [/=]:= const_prop_rv_m (erefl g) Hm (refl_equal rv).
  case: const_prop_rv => ??;case: const_prop_rv => ??.
  rewrite /RelationPairs.RelCompFun /= => /Hrec H ->.
  case: const_prop_rvs H => ??;case: const_prop_rvs => ?? [].
  by rewrite /RelationPairs.RelCompFun /= => -> ->.
Qed.

#[local]
Instance add_cpm_m :
  Proper (@Mvar_eq const_v ==> eq ==> eq ==> eq ==> eq ==> @Mvar_eq const_v) add_cpm.
Proof.
  move=> m1 m2 Hm x x' <- {x'} t t' <- {t'} ty ty' <- {ty'} e e' <- {e'}.
  case: x t => //= v [];rewrite ?Hm //.
  by case: e => //= [n | b | [] // sz [] // n ]; rewrite Hm.
Qed.

#[local]
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

#[local]
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

  Context (gd : glob_decls).

  Let Pr (i:instr_r) :=
    forall ii m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_ir gd m1 ii i) (const_prop_ir gd m2 ii i).

  Let Pi (i:instr) :=
    forall m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_i gd m1 i) (const_prop_i gd m2 i).

  Let Pc (c:cmd) :=
    forall m1 m2, Mvar_eq m1 m2 ->
    Mvarc_eq (const_prop (const_prop_i gd) m1 c) (const_prop (const_prop_i gd) m2 c).

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
    set g := if t is AT_inline then Some (assoc gd) else None.
    move=> ii m1 m2 /= Heq; have := const_prop_rv_m (erefl g) Heq (refl_equal x).
    rewrite /const_prop_ir.
    case: const_prop_rv => ??; case: const_prop_rv => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    by split => //=; rewrite /RelationPairs.RelCompFun /= Heq.
  Qed.

  Local Lemma Wopn xs t o es: Pr (Copn xs t o es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m (erefl None) Heq (refl_equal xs).
    rewrite /const_prop_ir.
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    have -> // : [seq const_prop_e None m1 i | i <- es] = [seq const_prop_e None m2 i | i <- es].
    by apply: map_ext => z _; rewrite Heq.
  Qed.

  Local Lemma Wsyscall xs o es: Pr (Csyscall xs o es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m (erefl None) Heq (refl_equal xs).
    rewrite /const_prop_ir.
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal; apply: map_ext => z _; rewrite Heq.
  Qed.

  Local Lemma Wif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> Hc1 Hc2 ii m1 m2 Heq /=.
    rewrite /const_prop_ir -/(const_prop_i _).
    have -> : const_prop_e None m1 e = const_prop_e None m2 e by rewrite Heq.
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
    rewrite /const_prop_ir -/(const_prop_i _).
    have -> : const_prop_e None m1 lo = const_prop_e None m2 lo by rewrite Heq.
    have -> : const_prop_e None m1 hi = const_prop_e None m2 hi by rewrite Heq.
    set ww1 := remove_cpm _ _; set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => ??; case: const_prop => ?? [].
    by rewrite /RelationPairs.RelCompFun /= Hw => _ ->.
  Qed.

  Local Lemma Wwhile a c e inf c': Pc c -> Pc c' -> Pr (Cwhile a c e inf c').
  Proof.
    move=> Hc Hc' ii m1 m2 Heq /=.
    rewrite /const_prop_ir -/const_prop_i.
    set ww1 := remove_cpm _ _;set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => m1' c1. case: const_prop => m2' c2 [].
    rewrite /RelationPairs.RelCompFun /= => H ->.
    move: (H) => /Hc'; case: const_prop => ?? ; case: const_prop => ?? [].
    rewrite /RelationPairs.RelCompFun /= => _ ->.
    have -> : const_prop_e None m1' e = const_prop_e None m2' e by rewrite H.
    by case: is_bool => //= ?; case:ifP.
  Qed.

  Local Lemma Wcall xs f es: Pr (Ccall xs f es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m (erefl None) Heq (refl_equal xs).
    rewrite /const_prop_ir.
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal; apply: map_ext => z _; rewrite Heq.
  Qed.

End PROPER.

Lemma const_prop_i_m :
  Proper (eq ==> @Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) const_prop_i.
Proof.
  move=> g _ <- m1 m2 Hm i1 i2 <-.
  exact:
    (instr_Rect (Wmk (gd:=g)) (Wnil g) (Wcons (gd:=g)) (Wasgn g) (Wopn g) (Wsyscall g)
       (Wif (gd:=g)) (Wfor (gd:=g)) (Wwhile (gd:=g)) (Wcall g)).
Qed.

Lemma const_prop_i_r_m :
  Proper (eq ==> @Mvar_eq const_v ==> eq ==> eq ==> @Mvarc_eq const_v) const_prop_ir.
Proof.
  move=> g _ <- m1 m2 Hm ii1 ii2 <- i1 i2 <-.
  exact:
    (instr_r_Rect (Wmk (gd:=g)) (Wnil g) (Wcons (gd:=g)) (Wasgn g) (Wopn g) (Wsyscall g)
       (Wif (gd:=g)) (Wfor (gd:=g)) (Wwhile (gd:=g)) (Wcall g)).
Qed.

Lemma const_prop_m g :
  Proper (@Mvar_eq const_v ==> eq ==> @Mvarc_eq const_v) (const_prop (const_prop_i g)).
Proof.
  move=> m1 m2 Hm c1 c2 <-.
  exact:
    (cmd_rect (Wmk (gd:=g)) (Wnil g) (Wcons (gd:=g)) (Wasgn g) (Wopn g) (Wsyscall g)
       (Wif (gd:=g)) (Wfor (gd:=g)) (Wwhile (gd:=g)) (Wcall g)).
Qed.

Lemma valid_cpm_m :
  Proper (eq ==> @Mvar_eq const_v ==> iff) valid_cpm.
Proof.
  move=> s? <- m m' Hm;split => H z n Hget;apply H.
  by rewrite Hm. by rewrite -Hm.
Qed.

Section PROOF.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : RelEvent E0}.

Variable (p:prog) (ev:extra_val_t).
Notation gd := (p_globs p).

Let p' := const_prop_prog p.

Definition uincl_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs_uincl fs1 fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fs_uincl fr1 fr2 |}.

Definition st_uincl (s : estate) (t : estate) :=
  [/\ escs s = escs t, emem s = emem t & vm_uincl (evm s) (evm t)].

Definition cmpl_inv (m : cpm) (s : estate) (t : estate) :=
  valid_cpm s.(evm) m /\ st_uincl s t.

Lemma st_uinclP s t : st_uincl s t <-> t = with_vm s (evm t) /\ vm_uincl (evm s) (evm t).
Proof.
  rewrite (surj_estate s) (surj_estate t) /=.
  by split => [ [/= <- <-] | [[<- <-] ?]].
Qed.

Lemma fs_uincl_syscall o : wrequiv fs_uincl (fexec_syscall o) (fexec_syscall o) fs_uincl.
Proof.
  rewrite /fexec_syscall => fs1 fs2 fr1 [<- <- hu1].
  t_xrbindP => -[[rscs m] vs1] hex.
  have [vs2 -> hu2] := exec_syscallP hex hu1.
  by move=> [<-] /=; eexists.
Qed.

Lemma valid_without_globals : valid_globs gd None.
Proof. by []. Qed.

Lemma const_prop_ePe m wdb e :
  wrequiv (cmpl_inv m) ((sem_pexpr wdb gd)^~ e)
    ((sem_pexpr wdb (p_globs p'))^~ (const_prop_e None m e)) value_uincl.
Proof.
  move=> s t v [hval /st_uinclP] []; move: (evm t) => vm1 -> hvm1.
  move=> /(const_prop_eP hval valid_without_globals) [v' [he' u1]].
  have [vs2 -> u2]:= sem_pexpr_uincl hvm1 he'.
  exists vs2 => //; apply: value_uincl_trans u1 u2.
Qed.

Lemma const_prop_esPe m wdb es :
  wrequiv (cmpl_inv m) ((sem_pexprs wdb gd)^~ es)
    ((sem_pexprs wdb (p_globs p'))^~ [seq const_prop_e None m i | i <- es]) (List.Forall2 value_uincl).
Proof.
  move=> s t vs [hval /st_uinclP] []; move: (evm t) => vm1 -> hvm1.
  move=> /(const_prop_esP hval valid_without_globals) [vs' hes' u1].
  have [vs2 -> u2]:= sem_pexprs_uincl hvm1 hes'.
  exists vs2 => //; apply: (Forall2_trans value_uincl_trans) u1 u2.
Qed.

Lemma const_prop_rvsPe m wdb xs vs1 vs2 :
  List.Forall2 value_uincl vs1 vs2 ->
  wrequiv (cmpl_inv m) (fun s => write_lvals wdb (p_globs p) s xs vs1)
                       (fun s => write_lvals wdb (p_globs p') s (const_prop_rvs None m xs).2 vs2)
          (cmpl_inv (const_prop_rvs None m xs).1).
Proof.
  move=> hu s t s' [hval /st_uinclP] []; move: (evm t) => vm1 -> hvm1 hw.
  have [hval' hw'] := const_prop_rvsP hval valid_without_globals hw.
  have [vm2 -> hvm2] := writes_uincl hvm1 hu hw'.
  eexists => //.
Qed.

(* FIXME this is generic is depend only on the previous lemma *)
Lemma const_prop_updP m wdb xs fs1 fs2 :
  fs_uincl fs1 fs2 →
  wrequiv (cmpl_inv m) (upd_estate wdb gd xs fs1) (upd_estate wdb (p_globs p') (const_prop_rvs None m xs).2 fs2)
        (cmpl_inv (const_prop_rvs None m xs).1).
Proof.
  rewrite /upd_estate => -[<- <- hu] s t s' [? [???]].
  by apply const_prop_rvsPe.
Qed.

  Let Pi i :=
    forall m,
      let mi := const_prop_i gd m i in
      wequiv_rec p p' ev ev uincl_spec (cmpl_inv m) [::i] mi.2 (cmpl_inv mi.1).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall m,
      let mc := const_prop (const_prop_i gd) m c in
      wequiv_rec p p' ev ev uincl_spec (cmpl_inv m) c mc.2 (cmpl_inv mc.1).

Lemma const_prop_sem_cond m e b :
  is_bool (const_prop_e None m e) = Some b ->
  ∀ (s1 s2 : estate) (v : bool), cmpl_inv m s1 s2 → sem_cond gd e s1 = ok v → v = b.
Proof.
  move=> heq s1 s2 b' [hm hu].
  rewrite /sem_cond; t_xrbindP => v he /to_boolI ?; subst v.
  have := const_prop_eP hm valid_without_globals he.
  by move: heq; case: is_boolP => // _ [->] /= [_ [[<-]]].
Qed.

Lemma cmpl_inv_remove m X s1 s2 :
  cmpl_inv m s1 s2 → cmpl_inv (remove_cpm m X) s1 s2.
Proof.
  move=> [hval hu]; split => //.
  by apply: valid_cpm_rm hval.
Qed.

Lemma remove_cpm_write c c2 X m mc P P' :
  let m' := remove_cpm m X in
  Sv.Subset (write_c c) X ->
  (forall s1 s2, P s1 s2 -> cmpl_inv m' s1 s2 /\ P' s1 s2) ->
  wequiv_rec p p' ev ev uincl_spec P' c c2 (cmpl_inv mc) ->
  wequiv_rec p p' ev ev uincl_spec P c c2 (fun s1 s2 => cmpl_inv m' s1 s2 /\ cmpl_inv mc s1 s2).
Proof.
  move=> m' hsub hPP' /wequiv_write hc.
  apply wkequivP' => s1_ s2_.
  move: (hc s1_); apply wkequiv_weaken => //.
  + by move=> _ _ [[-> ->] /hPP' []].
  move=> _ _ s1 s2 [[-> ->] /hPP' [[h1 _] _]] [heq [h2 ?]]; split => //; split => //.
  move=> x v h.
  have [_ hnin] := get_remove_cpm h.
  rewrite -heq; auto.
Qed.

Lemma remove_cpm_write1 c c2 X m mc P P':
  let m' := remove_cpm m X in
  Sv.Subset (write_c c) X ->
  (forall s1 s2, P s1 s2 -> cmpl_inv m' s1 s2 /\ P' s1 s2) ->
  wequiv_rec p p' ev ev uincl_spec P' c c2 (cmpl_inv mc) ->
  wequiv_rec p p' ev ev uincl_spec P c c2 (fun s1 s2 => cmpl_inv m' s1 s2).
Proof.
  move=> m' hsub hPP' hc.
  move: (remove_cpm_write hsub hPP' hc); apply wequiv_weaken => //; intuition.
Qed.

(* FIXME : move this it is generic *)
Lemma fs_uincl_initialize fs ft fd fd' s :
  f_tyin fd = f_tyin fd' ->
  f_extra fd = f_extra fd' ->
  f_params fd = f_params fd' ->
  fs_uincl fs ft ->
  initialize_funcall p ev fd fs = ok s ->
  exists2 t : estate, initialize_funcall p' ev fd' ft = ok t & st_uincl s t.
Proof.
  move=> hin hex hpar; case: fs ft => scs m vs [scs' m' vs'] [ /= h1 h2 h3].
  rewrite /initialize_funcall; t_xrbindP.
  rewrite -hin -hex -hpar /=.
  move=> vs1 /mapM2_dc_truncate_val -/(_ _ h3) [vs1' ->] hu ? /=.
  rewrite -h1 -h2 /estate0 /= => -> /= hw.
  have [vm2']:= [elaborate write_vars_uincl (vm_uincl_refl _) hu hw].
  rewrite with_vm_same => -> ?.
  by eexists.
Qed.

(* FIXME move this *)
Lemma wrequiv_finalize_funcall fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv st_uincl (finalize_funcall fd) (finalize_funcall fd') fs_uincl.
Proof.
  move=> hout hex hres s1 s2 fs [hscs hm hu]; rewrite /finalize_funcall -hres -hout -hex.
  t_xrbindP => vs /(get_var_is_uincl hu) [vs'] -> /= hvu vs2.
  move=> /mapM2_dc_truncate_val /(_ hvu) [vs2' ->] hvu2 <- /=.
  by rewrite hscs hm; eexists.
Qed.

Lemma is_update_immP xs o es x b e:
  is_update_imm xs o es = Some (x, b, e) ->
  [/\ xs = [::x], o = Oslh SLHupdate & es = [:: Pbool b; e]].
Proof.
  case: o => // -[] //.
  case: es => // -[] // b' [] // e' [] //.
  by case: xs => // x' [] // [] -> -> ->.
Qed.

Lemma it_const_prop_callP fn : wiequiv_f p p' ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
   apply wequiv_fun_ind => hrec {fn}.
   move=> fn _ fs ft [<- hfsu] fd hget.
   exists (const_prop_fun (p_globs p) fd).
   + by rewrite get_map_prog hget.
   move=> {hget}.
   exists (cmpl_inv empty_cpm),
          (cmpl_inv (const_prop (const_prop_i gd) empty_cpm (f_body fd)).1) => s1 hinit.
   have [hin hout hex hpar hres] :
       [/\ f_tyin fd = f_tyin (const_prop_fun gd fd)
         , f_tyout fd = f_tyout (const_prop_fun gd fd)
         , f_extra fd = f_extra (const_prop_fun gd fd)
         , f_params fd = f_params (const_prop_fun gd fd)
         & f_res fd = f_res (const_prop_fun gd fd)
        ].
   + by case fd => /= >; case: (const_prop _ _ _).
   have : exists2 t1, initialize_funcall p ev (const_prop_fun gd fd) ft = ok t1 &
                        cmpl_inv empty_cpm s1 t1.
   + by have [t h1 h2] := fs_uincl_initialize hin hex hpar hfsu hinit; exists t.
   move=> [t1 ht1 hinv]; exists t1; split => //; last first.
   + have := wrequiv_finalize_funcall hout hex hres.
     by apply wrequiv_weaken => // > [].
   have -> : f_body (const_prop_fun gd fd) = (const_prop (const_prop_i gd) empty_cpm (f_body fd)).2.
   + by case fd => /= >; case: const_prop.
   apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {fd fn fs hfsu hinit hin hout hex hpar hres hinv ht1 t1 ft s1}.
   + by move=> ?; apply wequiv_nil.
   + move=> i c hi hc m /=.
     have := hi m; case: const_prop_i => mi i' /= {}hi.
     have := hc mi; case: const_prop => mc c' /= {}hc.
     by rewrite -cat1s; apply wequiv_cat with (cmpl_inv mi).
   + move=> x tag ty e ii m /=.
     set globs := if tag is AT_inline then Some _ else None.
     case hrv : const_prop_rv => [m' x'] /=.
     apply wequiv_assgn_core.
     move=> s t s' hm; rewrite /sem_assgn; t_xrbindP => v he v' htr hwr.
     have Gv : valid_globs gd globs.
     + subst globs; case tag => //.
       clear => x gv v; rewrite /get_global /get_global_value => ->.
       by case: ifP => // _ /ok_inj <-.
     case: hm => Hm /st_uinclP []; move: (evm t) => vm1 -> hvm1.
     have [v1 [H U]] := const_prop_eP Hm Gv he.
     have [] := const_prop_rvP Hm Gv hwr.
     rewrite hrv /= => Hm' Hw'.
     have [v1' -> /= uv1']:= sem_pexpr_uincl hvm1 H.
     have [v2 htr2 hv']:= value_uincl_truncate U htr.
     have [v3 -> /= hv3]:= value_uincl_truncate uv1' htr2.
     have [vm2 -> hvm2]:= write_uincl hvm1 (value_uincl_trans hv' hv3) Hw'.
     eexists; first reflexivity.
     split => //.
     by apply: add_cpmP H U htr Hw' Hm'.
   + move=> xs tag o es ii m /=.
     rewrite (surjective_pairing (const_prop_rvs _ _ _)) /=.
     case heq : is_update_imm => [[[x b] e] | ].
     + have [{heq}hxs ho hes]:= is_update_immP heq.
       set Q := (cmpl_inv (const_prop_rvs None m xs).1).
       case: b hes => hes;
       rewrite /wequiv_rec /wequiv /=;
       (apply wkequiv_bind with Q; last by apply wkequiv_ret);
       apply wkequiv_iresult => s1 t1 s2 [hval /st_uinclP []];
       move: (evm t1) => vm1 ? hu; subst t1;
       rewrite /sem_sopn /sem_assgn; t_xrbindP => vs2_ vs1;
       move=> /(const_prop_esP hval valid_without_globals);
       rewrite hes ho ?hxs=> -[vs' Hes' Us] Ho;
       move=> /(const_prop_rvsP hval valid_without_globals) [] hval' hw;
       have [vs2 hs u2]:= sem_pexprs_uincl hu Hes';
       have [ vs3 ho' vs_vs3 ] := vuincl_exec_opn (Forall2_trans value_uincl_trans Us u2) Ho;
       have [vm2 {}hw U]:= writes_uincl hu vs_vs3 hw;
       move: hs => /=; t_xrbindP => _ ze he <- ?; subst vs2 => /=;
       move: ho'; rewrite ?he /exec_sopn /= /sopn_sem_ /= /se_move_sem; t_xrbindP;
       move=> z z0 h ? /= ?; subst vs3 z;
       move: hw; rewrite ?h /truncate_val /= ?truncate_word_u ?wrepr_unsigned hxs /=;
       t_xrbindP => ? -> -> /=; by eexists.
     apply wequiv_opn_uincl.
     + by apply const_prop_esPe.
     by apply const_prop_rvsPe.

   + move=> xs o es ii m /=.
     rewrite (surjective_pairing (const_prop_rvs _ _ _)) /=.
     apply wequiv_syscall_uincl.
     (* FIXME: this should be a generic lemma *)
     + by move=> s1 s2 [_ []].
     + by apply const_prop_esPe.
     + by apply fs_uincl_syscall.
     + by apply const_prop_updP.
   + move=> e c1 c2 hc1 hc2 ii m /=.
     case heq : is_bool => [b|].
     + apply wequiv_if_rcond with b.
       + by apply (const_prop_sem_cond heq).
       by case: (b); [apply hc1 | apply hc2].
     rewrite (surjective_pairing (const_prop _ _ _)) /=.
     rewrite (surjective_pairing (const_prop _ _ _)) /=.
     apply wequiv_if_uincl.
     + by apply const_prop_ePe.
     move=> b.
     apply wequiv_weaken with
       (cmpl_inv m) (cmpl_inv (const_prop (const_prop_i gd) m (if b then c1 else c2)).1) => //.
     + move=> s1 s2 [hval hu]; split => //.
       by apply merge_cpmP; case: b hval; auto.
     by case: b; [apply hc1 | apply hc2].
   + move=> i dir lo hi c hc ii m /=.
     set m' := remove_cpm _ _.
     have /= := hc m'.
     case: const_prop => mc c2 /= {}hc.
     apply wequiv_for_uincl with (cmpl_inv m').
     + by apply cmpl_inv_remove.
     1-2: by apply const_prop_ePe.
     + move => j s1 s2 s1' [hval /st_uinclP [-> hvm1]] Hw.
       have Hm' : valid_cpm (evm s1') m'.
       + have Hmi : Mvar_eq m' (Mvar.remove m' i).
         + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //].
           rewrite /m'; move: (remove_cpm_spec m (write_i (Cfor i (dir, lo, hi) c)) i).
           by case: Mvar.get => // a []; rewrite write_i_for;SvD.fsetdec.
         have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
         by apply: remove_cpm1P Hw hval.
       have /(_ _ _ (value_uincl_refl _)) [vm1' -> hvm1'] := write_var_uincl hvm1 _ Hw.
       by eexists.
     apply: remove_cpm_write1 hc => //.
     by rewrite write_i_for; SvD.fsetdec.
   + rewrite /Pc => a c e inf c' hc hc' ii m /=.
     set m' := remove_cpm m (write_i (Cwhile a c e inf c')).
     have := hc m'; case: const_prop => mc c2 /= {}hc.
     have := hc' mc; case: const_prop => mc' c2' /= {}hc'.
     set C := (X in wequiv_rec p p' ev ev uincl_spec _ _ X _).
     suff : [elaborate wequiv_rec p p' ev ev uincl_spec (cmpl_inv m') [:: MkI ii (Cwhile a c e inf c')] C (cmpl_inv mc)].
     + by apply wequiv_weaken => //; apply cmpl_inv_remove.
     have [[he ->]{C} | ->{C}] :
        (is_bool (const_prop_e None mc e) = Some false /\ C = c2) \/
        C = [:: MkI ii (Cwhile a c2 (const_prop_e None mc e) inf c2')].
     + by rewrite /C; case: is_boolP => [ [] | ]; auto.
     + apply wequiv_while_unroll.
       rewrite -(cats0 c2).
       apply wequiv_cat with (cmpl_inv mc) => //.
       apply wequiv_if_rcond with false.
       + by apply (const_prop_sem_cond he).
       by apply wequiv_nil.
     apply wkequivP' => s1_ s2_.
     suff : [elaborate
      wequiv_rec p p' ev ev uincl_spec (λ s1 s2, cmpl_inv m' s1 s2)
        [:: MkI ii (Cwhile a c e inf c')]
        [:: MkI ii (Cwhile a c2 (const_prop_e None mc e) inf c2')]
        (fun s1 s2 => cmpl_inv m' s1 s2 /\ cmpl_inv mc s1 s2)].
     + by apply wkequiv_weaken => //; intuition.
     apply wequiv_while_uincl => //.
     + eapply wrequiv_weaken; last (by apply const_prop_ePe); intuition.
     + by apply: remove_cpm_write hc => //; rewrite write_i_while; SvD.fsetdec.
     by apply: remove_cpm_write1 hc' => //; rewrite write_i_while; SvD.fsetdec.
   move=> xs f es ii m /=.
   rewrite (surjective_pairing (const_prop_rvs _ _ _)) /=.
   apply wequiv_call with (rpreF (eS:=uincl_spec)) (rpostF (eS:=uincl_spec)) (List.Forall2 value_uincl).
   + by apply const_prop_esPe.
   + by move=> s1 s2 vs1 vs2 [_ [???]?].
   + by apply hrec.
   by move=> fs1 fs2 fr1 fr2 _; apply const_prop_updP.
Qed.

End PROOF.

End WITH_PARAMS.

