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

(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)
Require Import Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import ZArith Utf8. 
        Import Relations.

Require Import sem compiler_util stack_alloc stack_sem.
Require Export linear linear_sem.
        Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Lemma is_labelP i lbl: reflect (i.(li_i) = Llabel lbl) (is_label lbl i).
Proof.
  case:i => ii [||l||] //=;try by constructor.
  by apply:(equivP (_ =P _));split=> [|[]] ->.
Qed.

Section CAT.

  Let Pi (i:instr) :=
    forall lbl l ,
     linear_i i lbl l =
     linear_i i lbl [::] >>= (fun (p:label*lcmd) => ok (p.1, p.2 ++ l)).

  Let Pr (i:instr_r) :=
    forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall lbl l ,
     linear_c linear_i c lbl l =
     linear_c linear_i c lbl [::] >>=
       (fun (p:label*lcmd) => ok (p.1, p.2 ++ l)).

  Let Pf (fd:fundef) := True.

  Let HmkI: forall i ii, Pr i -> Pi (MkI ii i).
  Proof. by []. Qed.

  Let Hskip : Pc [::].
  Proof. by []. Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc lbl l /=.
    rewrite Hc !bindA;apply bind_eq => //= p.
    by rewrite Hi (Hi p.1 p.2) bindA;apply bind_eq => //= p';rewrite catA.
  Qed.

  Let Hassgn : forall x t e, Pr (Cassgn x t e).
  Proof. by []. Qed.

  Let Hopn : forall xs o es, Pr (Copn xs o es).
  Proof. by []. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii lbl l /=.
    case Heq1: (c1)=> [|i1 l1].
    + by rewrite Hc2 (Hc2 _ [::_]) !bindA;apply bind_eq => //= p;rewrite -catA.
    rewrite -Heq1=> {Heq1 i1 l1};case Heq2: (c2)=> [|i2 l2].
    + by rewrite Hc1 (Hc1 _ [::_]) !bindA;apply bind_eq => //= p;rewrite -catA.
    rewrite -Heq2=> {Heq2 i2 l2}.
    rewrite Hc1 (Hc1 _ [::_]) !bindA;apply bind_eq => //= p.
    rewrite Hc2 (Hc2 _ [::_ & _])!bindA;apply bind_eq => //= p1.
    by rewrite -!catA /= -catA.
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Let Hwhile : forall c e c', Pc c -> Pc c' -> Pr (Cwhile c e c').
  Proof.
    move=> c e c' Hc Hc' ii lbl l /=.
    rewrite Hc (Hc _ [:: _]) !bindA; apply bind_eq => //= p.
    by rewrite Hc' (Hc' _ (_ :: _)) !bindA; apply bind_eq=> //= p'; rewrite -catA /= -catA /=.
  Qed.

  Let Hcall : forall i xs f es, Pr (Ccall i xs f es).
  Proof. by []. Qed.

  Lemma linear_i_nil i lbl l :
     linear_i i lbl l =
     linear_i i lbl [::] >>= (fun (p:label*lcmd) => ok (p.1, p.2 ++ l)).
  Proof.
    apply (@instr_Rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_c_nil c lbl l :
     linear_c linear_i c lbl l =
     linear_c linear_i c lbl [::] >>= (fun (p:label*lcmd) => ok (p.1, p.2 ++ l)).
  Proof.
    apply (@cmd_rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

End CAT.

Definition valid min max lc :=
  all (fun (i: linstr) => let (ii, ir) := i in match ir with
       | Llabel  lbl => ((min <=? lbl) && (lbl <? max))%positive
       | Lgoto   lbl => ((min <=? lbl) && (lbl <? max))%positive
       | Lcond _ lbl => ((min <=? lbl) && (lbl <? max))%positive
       | _           => true
       end) lc.

Lemma valid_cat min max lc1 lc2 :
  valid min max (lc1 ++ lc2) = valid min max lc1 && valid min max lc2.
Proof. by rewrite /valid all_cat. Qed.

Lemma valid_le_min min2 min1 max lc :
  (min1 <=? min2)%positive ->
  valid min2 max lc ->
  valid min1 max lc.
Proof.
  by move=> Hle1; apply: sub_all=> -[ii [| |lbl|lbl|e lbl]] //= /andP [] Hle2 ->;
  rewrite (Pos_leb_trans Hle1 Hle2).
Qed.

Lemma valid_le_max max2 max1 min lc :
  (max1 <=? max2)%positive ->
  valid min max1 lc ->
  valid min max2 lc.
Proof.
  by move=> Hle1; apply sub_all=> -[ii [| |lbl|lbl|e lbl]] //= /andP [] -> Hlt1 /=;
   rewrite (Pos_lt_leb_trans Hlt1 Hle1).
Qed.

Lemma le_next lbl : (lbl <=? next_lbl lbl)%positive.
Proof.
  by apply Pos.leb_le; have: (Zpos lbl <= Zpos lbl + 1)%Z by omega.
Qed.

Lemma lt_next lbl : (lbl <? next_lbl lbl)%positive.
Proof.
  by apply Pos.ltb_lt; have: (Zpos lbl < Zpos lbl + 1)%Z by omega.
Qed.

Lemma find_label_cat_tl c1 c2 lbl c:
  find_label lbl c1 = Some c -> find_label lbl (c1++c2) = Some (c++c2).
Proof.
  elim: c1=> //= i c1 Hrec;by case: ifP => [_[]<-|_/Hrec].
Qed.

Lemma lsem_cat_tl c2 c1 s1 s2 : lsem c1 s1 s2 ->
  lsem (c1++c2) (setc s1 (s1.(lc)++c2)) (setc s2 (s2.(lc)++c2)).
Proof.
  move=> H; elim H using lsem_ind; clear. once (econstructor; fail).
  move=> s1 s2 s3 Hsem1 _.
  apply: lsem_step.
  case: Hsem1 => {s1 s2 s3}.
  + by move=> [m1 vm1 c] s2 ii x tag e cs /= -> Heq2 /=; by apply: LSem_assgn.
  + move=> [m1 vm1 c] s2 ii xs o es cs /= -> Heq2 /=; by apply: LSem_opn.
  + move=> [m1 vm1 c] ii lbl cs /= -> /=.
    by apply: (@LSem_lbl (c1++c2) _ _ lbl (cs++c2)).
  + move=> [m1 vm1 c] ii lbl cs cs' /= -> Heq2.
    apply: (@LSem_goto (c1 ++ c2) _ _ lbl (cs++c2) (cs'++c2)) => //=.
    by apply: find_label_cat_tl.
  + move=> ii [m1 vm1 c] e lbl cs cs' /= -> Heq1 Heq2.
    apply: (@LSem_condTrue (c1 ++ c2) _ _ e lbl (cs++c2) (cs'++c2))=> //.
    by apply: find_label_cat_tl.
  + move=> ii [m1 vm1 c] e lbl cs /= -> Heq1.
    apply: (@LSem_condFalse (c1 ++ c2) _ _ e lbl (cs++c2))=> //.
Qed.

Lemma valid_find_label p1 p2 c c' lbl:
  valid p1 p2 c ->
  find_label lbl c = Some c' ->
  valid p1 p2 c'.
Proof.
  elim: c => //= -[ii [| b| lbl'|lbl'|e lbl']] l Hrec //= /andP[_ H];
    move:(H) => /Hrec H' //.
  by case:ifP => [_[]<-|_].
Qed.

Definition is_jump lbl (i:linstr) :=
 let (ii, ir) := i in
 match ir with
 | Lgoto lbl' => lbl == lbl'
 | Lcond _ lbl' => lbl == lbl'
 | _ => false
end.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2) = find_label lbl c2.
Proof.
  elim: c1 => //= i c1 Hrec Hdisj.
  have Hdisj' :  ~~ has (is_label lbl) c1.
  + by move: Hdisj;apply contra=> ->;rewrite orbC.
  have {Hrec}Hrec := Hrec Hdisj'.
  case:i Hdisj=> [ii [|b|lbl'|lbl'|e lbl']] //=;case:ifP => //= /eqP ?.
Qed.

Definition disjoint_lbl c1 c2 :=
  forall lbl, ~~(has (is_label lbl) c1 && has (is_jump lbl) c2).

Lemma disjoint_lbl_cons i c1 c2:
  disjoint_lbl c1 (i :: c2) -> disjoint_lbl c1 c2.
Proof.
  by move=> Hd lbl;apply: contra (Hd lbl)=> /= /andP[]->->;rewrite orbC.
Qed.

Lemma disjoint_find_label c1 c2 c lbl:
  disjoint_lbl c1 c2 ->
  find_label lbl c2 = Some c ->
  disjoint_lbl c1 c.
Proof.
  elim: c2 => //= i c2 Hrec Hd.
  have H:= (disjoint_lbl_cons Hd); have {Hrec}Hrec := Hrec H.
  by case:ifP => //= ? [] <-.
Qed.

Lemma lsem_cat_hd_aux c1 c2 s1 s2 :
  disjoint_lbl c1 c2 ->
  disjoint_lbl c1 s1.(lc) ->
  lsem c2 s1 s2 ->
  lsem (c1++c2) s1 s2.
Proof.
  move=> Hdisj2 Hdisjc Hsem; revert Hdisjc.
  elim Hsem using lsem_ind; clear -Hdisj2.
  + by move=> s1 Hdisjc; apply: rt_refl.
  move=> s1 s2 s3 Hsem1 _ Hrec Hdisjc.
  have [Hv1' Hsem1']: disjoint_lbl c1 (lc s2) /\ lsem1 (c1 ++ c2) s1 s2.
  + case: Hsem1 Hdisjc=> {Hrec s1 s2 s3}.
    + move=> [m1 vm1 c] s2 ii x tag e cs /= -> Heq2 /= H;split=> //.
      by apply: LSem_assgn.
    + move=> [m1 vm1 c] s2 ii xs o es cs /= -> Heq2 /= H;split=> //.
      by apply: LSem_opn.
    + move=> [m1 vm1 c] ii lbl cs /= -> /= H;split => //.
      by apply: (@LSem_lbl (c1++c2) _ _ lbl cs).
    + move=> [m1 vm1 c] ii lbl cs cs' /= -> Hf H;split.
      + by apply: disjoint_find_label Hf.
      apply: (@LSem_goto (c1 ++ c2) _ _ lbl cs cs')=> //.
      rewrite find_label_cat_hd //.
      by apply:contra (H lbl)=> /= ->;rewrite eq_refl.
    + move=> ii [m1 vm1 c] e lbl cs cs' /= -> Hcond Hf H; split.
      by apply: disjoint_find_label Hf.
      apply: (@LSem_condTrue (c1 ++ c2) _ _ e lbl cs cs')=> //.
      rewrite find_label_cat_hd //.
      by apply: contra (H lbl)=> /= ->;rewrite eq_refl.
    + move=> ii [m1 vm1 c] e lbl cs /= -> Hcond H; split.
      apply: disjoint_lbl_cons H.
      apply: (@LSem_condFalse (c1 ++ c2) _ _ e lbl cs)=> //.
  apply: lsem_step; eauto.
Qed.

Lemma lsem_cat_hd c1 c2 s1 s2 :
  disjoint_lbl c1 c2 ->
  (lc s1) = c2 ->
  lsem c2 s1 s2 ->
  lsem (c1++c2) s1 s2.
Proof. by move=> Hdisj Heq; apply: (lsem_cat_hd_aux Hdisj _);rewrite Heq. Qed.

Lemma valid_has c lbl p1 p2 :
  valid p1 p2 c -> has (is_label lbl) c || has (is_jump lbl) c ->
  ((p1 <=? lbl) && (lbl <? p2))%positive.
Proof.
  elim: c => //= i c Hrec /andP[] H /Hrec.
  by case: i H=>[ii [| |lbl'|lbl'|e lbl']] //=;
  rewrite {2}/is_label /=; case: eqP=> [->|].
Qed.

Lemma valid_disjoint p1 p2 p3 p4 c1 c2 :
  ((p2 <=? p3) || (p4 <=? p1))%positive ->
  valid p1 p2 c1 ->
  valid p3 p4 c2 ->
  disjoint_lbl c1 c2.
Proof.
  move=> Hp Hv1 Hv2 lbl;apply /negP=>/andP[] H1 H2.
  have := @valid_has _ lbl _ _ Hv1;rewrite H1=> /(_ isT) /andP[]/P_leP ? /P_ltP ?.
  have := @valid_has _ lbl _ _ Hv2;rewrite H2 orbT => /(_ isT) /andP[]/P_leP ? /P_ltP ?.
  case/orP: Hp => /P_leP ?;omega.
Qed.

Lemma disjoint_cat_l c1 c2 c :
  disjoint_lbl (c1++c2) c <-> (disjoint_lbl c1 c /\ disjoint_lbl c2 c).
Proof.
  rewrite /disjoint_lbl;split.
  + move=> H1;split=> lbl;have := H1 lbl;rewrite has_cat;apply contra=>/andP[]->->//.
    by rewrite orbC.
  move=> [H1 H2] lbl;rewrite has_cat;apply /negP => /andP[]/orP []H H'.
  + by move: (H1 lbl);rewrite H H'.
  by move: (H2 lbl);rewrite H H'.
Qed.

Lemma disjoint_cat_r c1 c2 c :
  disjoint_lbl c (c1++c2) <-> (disjoint_lbl c c1 /\ disjoint_lbl c c2).
Proof.
  rewrite /disjoint_lbl;split.
  + move=> H1;split=> lbl;have := H1 lbl;rewrite has_cat;apply contra=>/andP[]->->//.
    by rewrite orbC.
  move=> [H1 H2] lbl;rewrite has_cat;apply /negP => /andP[] H /orP[]H'.
  + by move: (H1 lbl);rewrite H H'.
  by move: (H2 lbl);rewrite H H'.
Qed.

Definition LSem_step c s1 s2 : lsem1 c s1 s2 -> lsem c s1 s2 := rt_step _ _ s1 s2.

(* TODO: move *)
Lemma sem_op1_b_dec v s e f:
  Let v1 := sem_pexpr s e in sem_op1_b f v1 = ok v ->
  exists z, Vbool (f z) = v /\ sem_pexpr s e = ok (Vbool z).
Proof.
  rewrite /sem_op1_b /mk_sem_sop1.
  t_xrbindP=> -[] //.
  + by move=> b -> b1 []<- <-; exists b; split.
  + by move=> [] //.
Qed.

Lemma sem_op2_b_dec v s e1 e2 f:
  Let v1 := sem_pexpr s e1 in (Let v2 := sem_pexpr s e2 in sem_op2_b f v1 v2) = ok v ->
  exists z1 z2, Vbool (f z1 z2) = v /\ sem_pexpr s e1 = ok (Vbool z1) /\ sem_pexpr s e2 = ok (Vbool z2).
Proof.
  t_xrbindP=> v1 Hv1 v2 Hv2; rewrite /sem_op2_b /mk_sem_sop2.
  t_xrbindP=> z1 Hz1 z2 Hz2 Hv.
  move: v1 Hv1 Hz1=> [] //; last by move=> [].
  move=> w1 Hw1 []Hz1; subst w1.
  move: v2 Hv2 Hz2=> [] //; last by move=> [].
  move=> w2 Hw2 []Hz1; subst w2.
  rewrite /sem_pexprs /= Hw1 /= Hw2 /=; eexists; eexists; eauto.
Qed.

Lemma sem_op1_w_dec v s e f:
  Let v1 := sem_pexpr s e in sem_op1_w f v1 = ok v ->
  exists z, Vword (f z) = v /\ sem_pexpr s e = ok (Vword z).
Proof.
  t_xrbindP=> v1 Hv1; rewrite /sem_op1_w /mk_sem_sop1.
  t_xrbindP=> z1 Hz1 Hv.
  move: v1 Hv1 Hz1=> [] //; last by move=> [].
  move=> w1 Hw1 []Hz1; subst w1; eauto.
Qed.

Lemma of_val_same_type v1 v2 y:
  of_val (type_of_val v1) v2 = ok y ->
  type_of_val v1 = type_of_val v2.
Proof.
  move: v1 y=> [b|z|n a|w|[]] /= y; move: v2=> [b2|z2|n2 a2|w2|[]] //=.
  + case: (CEDecStype.pos_dec _ _)=> [H _|//]; by rewrite H.
  + by move=> p; case: (n == p).
  + move=> a.
    case: (CEDecStype.pos_dec _ _)=> [H _|//]; by rewrite H.
  + move=> p ?; by case: (_ == _).
Qed.

Lemma snot_spec s e v:
  sem_pexpr s e = ok v ->
  type_of_val v = sbool ->
  sem_pexpr s (snot e) = sem_pexpr s (Papp1 Onot e).
Proof.
  elim: e v=> //.
  + move=> [] // e He v /sem_op1_b_dec /= [z [<- ->]] /= _.
    by move: z=> [].
  + move=> [] // e1 He1 e2 He2 v /sem_op2_b_dec /= [z1 [z2 [Hz [Hz1 Hz2]]]] _.
    + rewrite (He1 _ Hz1) // (He2 _ Hz2) //= Hz1 Hz2 /=.
      rewrite /sem_op2_b /sem_op1_b /mk_sem_sop2 /mk_sem_sop1 /=.
      by rewrite negb_and.
    + rewrite (He1 _ Hz1) // (He2 _ Hz2) //= Hz1 Hz2 /=.
      rewrite /sem_op2_b /sem_op1_b /mk_sem_sop2 /mk_sem_sop1 /=.
      by rewrite negb_or.
  + move=> e _ e1 He1 e2 He2 v /=.
    t_xrbindP=> b bv Hbv Hb b1 Hb1 b2 Hb2 y1 Hy1 y2 Hy2 <- Hv.
    rewrite Hbv /= Hb /=.
    have Ht := of_val_same_type Hy2.
    have H1: type_of_val b1 = sbool.
      by move: b Hb Hv=> [] // _ <-.
    have H2: type_of_val b2 = sbool.
      by move: b Hb Hv=> [] // _ <-.
    rewrite (He1 _ Hb1) //= (He2 _ Hb2) //= Hb1 /= Hb2 /=.
    rewrite Hy2 /= Hy1 /=.
    rewrite H1 /= in y1, Hy1, y2, Hy2.
    rewrite /sem_op1_b /mk_sem_sop1 /= Hy1 Hy2 /=.
    by case: (b); rewrite ?Hy1 // Hy2.
Qed.

Section PROOF.

  Variable p:  sprog.
  Variable p': lprog.
  Hypothesis linear_ok : linear_prog p = ok p'.

  Let Pi (i:instr) :=
    forall lbl lbli li, linear_i i lbl [::] = ok (lbli, li) ->
    [/\ (lbl <=? lbli)%positive,
     valid lbl lbli li &
     forall s1 s2, S.sem_I p s1 i s2 ->
       lsem li (of_estate s1 li) (of_estate s2 [::])].

  Let Pi_r (i:instr_r) :=
    forall ii lbl lbli li, linear_i (MkI ii i) lbl [::] = ok (lbli, li) ->
    [/\ (lbl <=? lbli)%positive,
     valid lbl lbli li &
     forall s1 s2, S.sem_i p s1 i s2 ->
       lsem li (of_estate s1 li) (of_estate s2 [::])].

  Let Pc (c:cmd) :=
    forall lbl lblc lc, linear_c linear_i c lbl [::] = ok (lblc, lc) ->
    [/\ (lbl <=? lblc)%positive,
     valid lbl lblc lc &
     forall s1 s2, S.sem p s1 c s2 ->
       lsem lc (of_estate s1 lc) (of_estate s2 [::])].

  Let HmkI : forall i ii, Pi_r i -> Pi (MkI ii i).
  Proof.
    move=> i ii Hi_r lbl lbli li Hli.
    move: Hi_r=> /(_ ii lbl lbli li Hli) [H1 H2 H3]; split=> //.
    move=> s1 s2 Hs.
    by sinversion Hs; apply: H3.
  Qed.

  Let Hskip : Pc [::].
  Proof.
    move=> lbl lbli li /= [] <- <-;split=> //. apply Pos.leb_refl.
    move=> s1 s2 H;inversion H;clear H;subst; apply: rt_refl.
  Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc lbl lbl' l' /=.
    case Heqc: linear_c => [[lblc lc]|] //=.
    have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ Heqc.
    rewrite linear_i_nil.
    case Heqi: linear_i => [[lbli li]|] //= []??;subst lbl' l'.
    have {Hi}[Hle2 Hvi Hi]:= Hi _ _ _ Heqi;split.
    + by apply /P_leP;move/P_leP: Hle1;move/P_leP: Hle2=> ??;omega.
    + by rewrite valid_cat (valid_le_min Hle1 Hvi) (valid_le_max Hle2 Hvc).
    move=> [m1 vm1] s2 H;inversion H;clear H;subst.
    case: s0 H3 H5 => m2 vm2 H3 H5.
    apply (@lsem_trans (of_estate {| emem := m2; evm := vm2 |} lc)).
    + by apply (lsem_cat_tl lc (Hi _ _ H3)).
    have Hvc1 : valid 1 lblc lc.
    apply: valid_le_min Hvc.
    + by rewrite /is_true Pos.leb_le;apply Pos.le_1_l.
    apply: lsem_cat_hd=>//.
    + by apply: valid_disjoint Hvi Hvc;rewrite Pos.leb_refl orbC.
    by apply: Hc H5.
  Qed.

  Let Hassgn : forall x e tag, Pi_r (Cassgn x e tag).
  Proof.
    move=> x e tag ii lbl lbl' l' [] <- <-;rewrite Pos.leb_refl;split=>//.
    move=> -[m1 vm1] s2 H;inversion H;clear H;subst;apply LSem_step.
    eapply LSem_assgn=> /=; eauto.
  Qed.

  Let Hopn : forall xs o es, Pi_r (Copn xs o es).
  Proof.
    move=> x e tag ii lbl lbl' l' [] <- <-;rewrite Pos.leb_refl;split=>//.
    move=> -[m1 vm1] s2 H;inversion H;clear H;subst;apply LSem_step.
    eapply LSem_opn=> /=; eauto.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi_r (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii lbl lbl' l' /=.
    case Heq1: (c1)=> [|i1 l1].
    + subst;rewrite linear_c_nil;case Heq: linear_c => [[lbl2 lc2]|] //= [] <- <-.
      have Hlen := le_next lbl.
      have [Hle Hv2 Hs2]:= Hc2 _ _ _ Heq;split.
      + by apply: Pos_leb_trans Hle.
      + rewrite /= valid_cat Pos.leb_refl (valid_le_min Hlen Hv2) /= Pos.leb_refl.
        by rewrite (Pos_lt_leb_trans (lt_next _) Hle).
      move=> [m1 vm1] s2 H;inversion H;clear H;subst.
      + apply: lsem_step.
        apply: LSem_condTrue=> //.
        rewrite -cat_cons.
        rewrite find_label_cat_hd.
        by rewrite /= /is_label /= eq_refl.
        apply /negP=> H.
        rewrite /= in H.
        have := @valid_has _ lbl _ _ Hv2; rewrite H=> /(_ isT) /andP[].
        by rewrite Pos.leb_antisym lt_next.
        sinversion H6.
        exact: rt_refl.
      + apply: lsem_step.
        apply: LSem_condFalse=> //.
        have {Hs2}Hs2:= Hs2 _ _ H6.
        have Hvc : valid lbl (next_lbl lbl) [:: MkLI ii (Lcond e lbl)].
        + by rewrite /= Pos.leb_refl lt_next.
        have Hd: disjoint_lbl [:: MkLI ii (Lcond e lbl)] lc2 by move=> ?.
        have /(_ (erefl _)):= @lsem_cat_hd [:: MkLI ii (Lcond e lbl)] lc2 _ _ Hd _ Hs2.
        move=> /(@lsem_cat_tl [:: MkLI ii (Llabel lbl)]) Hsem.
        apply (lsem_trans Hsem);case s2 => m2 vm2.
        by apply LSem_step;apply: LSem_lbl.
    rewrite -Heq1 => {Heq1 l1 i1};case Heq2: c2 => [|i2 l2].
    + subst;rewrite linear_c_nil;case Heq: linear_c => [[lbl1 lc1]|] //= [] <- <-.
      have Hlen := le_next lbl.
      have [Hle Hv1 Hs1]:= Hc1 _ _ _ Heq;split.
      + by apply: Pos_leb_trans Hle.
      + rewrite /= valid_cat Pos.leb_refl (valid_le_min Hlen Hv1) /= Pos.leb_refl.
        by rewrite (Pos_lt_leb_trans (lt_next _) Hle).
      move=> [m1 vm1] s2 H;inversion H;clear H;subst.
      + apply: lsem_step.
        apply: LSem_condFalse=> //=.
        apply: rbindP H5=> -[] // w H1 //.
        + by rewrite (snot_spec H1) //= H1 /= => -[]->.
        by move: w H1=> [].
        have {Hs1}Hs1:= Hs1 _ _ H6.
        have Hvc : valid lbl (next_lbl lbl) [:: MkLI ii (Lcond (Papp1 Onot e) lbl)].
        + by rewrite /= Pos.leb_refl lt_next.
        have Hd: disjoint_lbl [:: MkLI ii (Lcond (snot e) lbl)] lc1 by move=> ?.
        have /(_ (erefl _)):= @lsem_cat_hd [:: MkLI ii (Lcond (snot e) lbl)] lc1 _ _ Hd _ Hs1.
        move=> /(@lsem_cat_tl [:: MkLI ii (Llabel lbl)]) Hsem.
        apply (lsem_trans Hsem);case s2 => m2 vm2.
        by apply LSem_step;apply: LSem_lbl.
      + apply: lsem_step.
        apply: LSem_condTrue=> //=.
        apply: rbindP H5=> -[] // w H1 //.
        + by rewrite (snot_spec H1) //= H1 /= => -[]->.
        by move: w H1=> [].
        rewrite find_label_cat_hd //=.
        by rewrite /is_label /= eq_refl.
        apply/negP=> H.
        have := @valid_has _ lbl _ _ Hv1; rewrite H=> /(_ isT) /andP[].
        by rewrite Pos.leb_antisym lt_next.
        sinversion H6.
        exact: rt_refl.
    rewrite -Heq2 => {Heq2 l2 i2}.
    rewrite linear_c_nil;case Heq1: linear_c => [[lbl1 lc1]|] //=.
    rewrite linear_c_nil;case Heq2: linear_c => [[lbl2 lc2]|] //= [] <- <-.
    have leL1 := le_next lbl; have leL2 := le_next (next_lbl lbl).
    have [Hle1 Hv1 Hs1]:= Hc1 _ _ _ Heq1;have [Hle2 Hv2 Hs2]:= Hc2 _ _ _ Heq2.
    have L2lbl2 := Pos_leb_trans Hle1 Hle2.
    have L1lbl2 := Pos_leb_trans leL2 L2lbl2.
    have lblL2 := Pos_leb_trans leL1 leL2.
    have lbllbl1 := Pos_leb_trans lblL2 Hle1;split.
    + by apply: Pos_leb_trans Hle2.
    + rewrite /= valid_cat /= valid_cat /=.
      rewrite Pos.leb_refl leL1 (Pos_lt_leb_trans (lt_next lbl) L1lbl2).
      rewrite (Pos_lt_leb_trans (lt_next _) L2lbl2).
      by rewrite (valid_le_min _ Hv2) // (valid_le_max Hle2 (valid_le_min lblL2 Hv1)).
    move=> [m1 vm1] s2 H;inversion H;clear H;subst.
    + apply lsem_step with (of_estate {| emem := m1; evm := vm1 |} (lc1 ++ [:: MkLI ii (Llabel (next_lbl lbl))])).
      + apply: LSem_condTrue=> //=.
        rewrite find_label_cat_hd /= /is_label /= ?eq_refl //.
        apply /negP => H; have := @valid_has _ lbl _ _ Hv2;rewrite H=> /(_ isT) /andP[].
        have Hlt := Pos_leb_trans leL2 Hle1.
        by rewrite Pos.leb_antisym (Pos_lt_leb_trans(lt_next _)(Pos_leb_trans leL2 Hle1)).
      have {Hs1}Hs1 := Hs1 _ _ H6.
      have Hd:
        disjoint_lbl ([:: MkLI ii (Lcond e lbl)]++lc2++[:: MkLI ii (Lgoto (next_lbl lbl)); MkLI ii (Llabel lbl)]) lc1.
      + rewrite !disjoint_cat_l;split;first by move=> ?.
        split;first by apply: valid_disjoint Hv2 Hv1;rewrite Pos.leb_refl orbC.
        move=> lbl0 /=;rewrite orbF /is_label /=;case:eqP=> //= ?;subst lbl0.
        apply /negP => H; have := @valid_has _ lbl _ _ Hv1;rewrite H orbT.
        move=> /(_ isT) /andP[];rewrite Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (lt_next _) leL2).
      have /(_ (erefl _)):= lsem_cat_hd Hd _ Hs1.
      move=> /(@lsem_cat_tl [:: MkLI ii (Llabel (next_lbl lbl))]) /=.
      rewrite -!catA /= => Hsem; apply (lsem_trans Hsem).
      by apply LSem_step;apply: LSem_lbl.
    + apply lsem_step with (of_estate {| emem := m1; evm := vm1 |} (lc2 ++ [:: MkLI ii (Lgoto (next_lbl lbl)), MkLI ii (Llabel lbl) & lc1 ++ [:: MkLI ii (Llabel (next_lbl lbl))]])).
      + apply: LSem_condFalse=> //.
      apply lsem_trans with (of_estate s2 [:: MkLI ii (Lgoto (next_lbl lbl)), MkLI ii (Llabel lbl) & lc1 ++ [:: MkLI ii (Llabel (next_lbl lbl))]]).
      + have := Hs2 _ _ H6.
        move=> /(@lsem_cat_tl [:: MkLI ii (Lgoto (next_lbl lbl)), MkLI ii (Llabel lbl) & lc1 ++ [:: MkLI ii (Llabel (next_lbl lbl))]]) /= H.
        by have /= /(_ [:: MkLI ii (Lcond e lbl)]) H0:= lsem_cat_hd _ _ H;apply H0.
      apply LSem_step. eapply LSem_goto=> /=;eauto.
      rewrite find_label_cat_hd /= /is_label /=.
      + case: eqP => Heq.
        + by have := lt_next lbl;rewrite Pos.ltb_antisym Heq Pos.leb_refl.
        rewrite find_label_cat_hd /= /is_label /= ?eq_refl //.
        apply /negP=> H;have := @valid_has _ (next_lbl lbl) _ _ Hv1.
        by rewrite H Pos.leb_antisym lt_next /= => /(_ isT).
      apply /negP=> H;have := @valid_has _ (next_lbl lbl) _ _ Hv2.
      by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) Hle1) /= => /(_ isT).
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pi_r (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Let Hwhile : forall c e c', Pc c -> Pc c' -> Pi_r (Cwhile c e c').
  Proof.
    move=> c e c' Hc Hc' ii lbl lbli li /=;rewrite linear_c_nil.
    case Heqc: linear_c => [[lblc lc]|] //=.
    have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ Heqc.
    rewrite linear_c_nil.
    case Heq:linear_c => [[lblc' lc']|] //= [] ??;subst lbli li.
    have leL1 := le_next lbl; have leL2 := le_next (next_lbl lbl).
    have lblL2 := Pos_leb_trans leL1 leL2.
    have lblcL2 := Pos_leb_trans lblL2 Hle1.
    have {Heq} [Hle Hv Hs]:= Hc' _ _ _ Heq;split.
    + apply: (Pos_leb_trans lblL2).
      by apply: (Pos_leb_trans Hle1).
    + rewrite /= valid_cat /= Pos.leb_refl leL1 (valid_le_min _ Hv) //.
      rewrite (Pos_lt_leb_trans (lt_next _)).
      rewrite (Pos_lt_leb_trans _ Hle) /=.
      rewrite valid_cat /= leL1 /=.
      rewrite (valid_le_max Hle) /=.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans Hle1) //.
      rewrite (valid_le_min _ Hvc) //.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans _ Hle) //.
      rewrite (Pos_leb_trans leL2 Hle1) //.
    move=> s1 s2 H.
    + apply lsem_step with (of_estate s1 (lc ++ [::MkLI ii (Lcond e (next_lbl lbl))])).
      + eapply LSem_goto=> /=;eauto.
        rewrite /is_label /=.
        case: eqP => H'.
        + by have := lt_next lbl;rewrite Pos.ltb_antisym -H' Pos.leb_refl.
        rewrite find_label_cat_hd /= ?eq_refl //.
        rewrite /is_label /=.
        case: eqP => //.
        apply /negP=> H1;have := @valid_has _ lbl _ _ Hv.
        rewrite H1 Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (Pos_lt_leb_trans (lt_next _) leL2) Hle1) /= => /(_ isT).
    (* Start induction after the first goto (at the first location where the loop will come back) *)
    set C1 := lc' ++ (MkLI ii (Llabel lbl) :: lc) ++ [:: MkLI ii (Lcond e (next_lbl lbl))];
    set C2 := [:: MkLI ii (Lgoto lbl), MkLI ii (Llabel (next_lbl lbl)) & C1].
    elim: _ {-1}_ _ / H Hs (erefl (Cwhile c e c'))=> // {s1 s2}.
    + move=> s1 s2 s3 s4 c0 e0 c'0 Hsem0 He Hsem Hsemi IH Hs [] ???; subst c0; subst e0; subst c'0.
      apply (@lsem_trans (of_estate s2 [ :: MkLI ii (Lcond e (next_lbl lbl))])).
      + have Hd: disjoint_lbl
          [:: {| li_ii := ii; li_i := Lgoto lbl |}, {| li_ii := ii; li_i := Llabel (next_lbl lbl) |}
          & lc' ++ [:: {| li_ii := ii; li_i := Llabel lbl |}]] lc.
          rewrite -cat1s -[_ :: (lc' ++ _)]cat1s.
          rewrite !disjoint_cat_l; repeat split=> //.
          + move=> lbl0 /=;rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply /negP=> H; have := @valid_has _ (next_lbl lbl) _ _ Hvc.
            by rewrite H Pos.leb_antisym (lt_next _) orbT=> /(_ isT).
          + apply: (valid_disjoint _ Hv Hvc).
            by rewrite Pos.leb_refl /= orbT.
          + move=> lbl0 /=; rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply/negP=> H; have := @valid_has _ lbl _ _ Hvc.
            by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) leL2) orbT=> /(_ isT).
        have /(_ (erefl _)) := lsem_cat_hd Hd _ (Hc _ _ Hsem0).
        move=> /(lsem_cat_tl [:: MkLI ii (Lcond e (next_lbl lbl))]) /=.
        have ->: [:: {| li_ii := ii; li_i := Lgoto lbl |}, {| li_ii := ii; li_i := Llabel (next_lbl lbl) |} & ((lc' ++ [:: {| li_ii := ii; li_i := Llabel lbl |}]) ++ lc) ++ [:: {| li_ii := ii; li_i := Lcond e (next_lbl lbl) |}]] = C2.
          rewrite /C2.
          congr [:: _, _ & _].
          rewrite /C1 !catA.
          by rewrite -!catA cat1s.
        move=> Hsem'; apply: Hsem'.
      apply: lsem_step.
      apply: LSem_condTrue=> //.
      rewrite /= /to_estate /=.
      by case: s2 He Hsem Hsem0.
      by rewrite /= /is_label /= eq_refl.
      apply: lsem_trans.
      have Hd : disjoint_lbl [:: MkLI ii (Lgoto lbl); MkLI ii (Llabel (next_lbl lbl))] lc'.
      + move=> lbl0 /=;rewrite orbF /is_label /=;case: eqP => //= ?;subst.
        apply /negP=> H;have := @valid_has _ (next_lbl lbl) _ _ Hv.
        rewrite H Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (lt_next _) Hle1) /= orbT => /(_ isT).
      have /(_ (erefl _)):= lsem_cat_hd Hd _ (Hs _ _ Hsem).
      move=> /(@lsem_cat_tl ((MkLI ii (Llabel lbl)) :: lc ++ [:: MkLI ii (Lcond e (next_lbl lbl))])).
      rewrite /= -/C2 => H.
      apply: (lsem_trans H);apply: LSem_step.
      eapply LSem_lbl=> /=; eauto.
      exact: IH.
    + move=> s1 s2 c0 e0 c0' Hs0 He Hs [] ???; subst e0 c0 c0'.
      apply (@lsem_trans (of_estate s2 [ :: MkLI ii (Lcond e (next_lbl lbl))])).
      + have Hd: disjoint_lbl
          [:: {| li_ii := ii; li_i := Lgoto lbl |}, {| li_ii := ii; li_i := Llabel (next_lbl lbl) |}
          & lc' ++ [:: {| li_ii := ii; li_i := Llabel lbl |}]] lc.
          rewrite -cat1s -[_ :: (lc' ++ _)]cat1s.
          rewrite !disjoint_cat_l; repeat split=> //.
          + move=> lbl0 /=;rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply /negP=> H; have := @valid_has _ (next_lbl lbl) _ _ Hvc.
            by rewrite H Pos.leb_antisym (lt_next _) orbT=> /(_ isT).
          + apply: (valid_disjoint _ Hv Hvc).
            by rewrite Pos.leb_refl /= orbT.
          + move=> lbl0 /=; rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply/negP=> H; have := @valid_has _ lbl _ _ Hvc.
            by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) leL2) orbT=> /(_ isT).
        have /(_ (erefl _)) := lsem_cat_hd Hd _ (Hc _ _ Hs0).
        move=> /(lsem_cat_tl [:: MkLI ii (Lcond e (next_lbl lbl))]) /=.
        have ->: [:: {| li_ii := ii; li_i := Lgoto lbl |}, {| li_ii := ii; li_i := Llabel (next_lbl lbl) |} & ((lc' ++ [:: {| li_ii := ii; li_i := Llabel lbl |}]) ++ lc) ++ [:: {| li_ii := ii; li_i := Lcond e (next_lbl lbl) |}]] = C2.
          rewrite /C2.
          congr [:: _, _ & _].
          rewrite /C1 !catA.
          by rewrite -!catA cat1s.
        move=> Hsem'; apply: Hsem'.
      apply: lsem_step.
      apply: LSem_condFalse=> //.
      rewrite /= /to_estate /=.
      by case: s2 He Hs0.
      exact: rt_refl.
  Qed.

  Let Hcall : forall i xs f es, Pi_r (Ccall i xs f es).
  Proof. by []. Qed.

  Lemma linear_cP c lbl lblc lc:
    linear_c linear_i c lbl [::] = ok (lblc, lc) ->
    [/\ (lbl <=? lblc)%positive,
     valid lbl lblc lc &
     forall s1 s2, S.sem p s1 c s2 ->
       lsem lc (of_estate s1 lc) (of_estate s2 [::])].
  Proof.
    apply (@cmd_rect Pi_r Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_fdP:
    forall fn m1 va m2 vr,
    S.sem_call p m1 fn va m2 vr -> lsem_fd p' m1 fn va m2 vr.
  Proof.
    move=> fn m1 va m2 vr H.
    sinversion H.
    have H0' := linear_ok.
    rewrite /linear_prog in H0'.
    have [f' [Hf'1 Hf'2]] := (get_map_cfprog H0' H0).
    have Hf'3 := Hf'1.
    apply: rbindP Hf'3=> [l Hc] [] Hf'3.
    rewrite /add_finfo in Hc.
    case Heq: linear_c Hc=> [[lblc lc]|] //= [] Hl.
    rewrite linear_c_nil in Heq.
    apply: rbindP Heq=> [[lblc' lc']] Heq [] Hz1 Hz2.
    have [_ _ H] := linear_cP Heq.
    move: H4=> /H /(@lsem_cat_tl [::]) Hs.
    rewrite -Hf'3 in Hf'2.
    apply: LSem_fd; eauto=> /=.
    rewrite -Hl /=.
    rewrite /= Hz2 in Hs.
    exact: Hs.
  Qed.

End PROOF.
