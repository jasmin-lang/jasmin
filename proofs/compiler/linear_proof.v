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
From Coq
Require Import Setoid Morphisms Lia.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Utf8.
        Import Relations.

Require sem_one_varmap_facts.
Import ssrZ.
Import psem psem_facts sem_one_varmap compiler_util sem_one_varmap_facts.
Require Export linear linear_sem.
Import x86_variables.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move *)
Lemma pword_of_word_uincl sz (x: word sz) (y: pword sz) :
  @pval_uincl (sword sz) (sword sz) (pword_of_word x) y →
  ∃ e : sz = pw_size y, pw_word y = ecast _ _ e x.
Proof.
  case: y => sz' y sz'_le_sz.
  case/andP => /(cmp_le_antisym sz'_le_sz) ? /=; subst.
  move => /eqP -> {x}; exists erefl.
  by rewrite zero_extend_u.
  Qed.

Lemma wunsigned_sub_small (p: pointer) (n: Z) :
  (0 <= n < wbase Uptr →
   wunsigned (p - wrepr Uptr n) <= wunsigned p →
   wunsigned (p - wrepr Uptr n) = wunsigned p - n)%Z.
Proof.
  rewrite -wrepr_opp wunsigned_repr => n_range.
  rewrite -/(wunsigned (wrepr _ _)) wunsigned_repr.
  change (word.modulus (wsize_size_minus_1 Uptr).+1) with (wbase Uptr).
  rewrite Zplus_mod_idemp_r.
  rewrite -/(wunsigned p).
  have := wunsigned_range p.
  move: (wunsigned p) => {p} p.
  elim_div. case; first by [].
  move: n_range.
  change (wbase Uptr) with 18446744073709551616%Z.
  lia.
Qed.

Local Open Scope seq_scope.

Lemma all_has {T} (p q: pred T) (s: seq T) :
  all p s →
  has q s →
  exists2 t, List.In t s & p t && q t.
Proof.
  elim: s => // t s ih /= /andP[] pt ps /orP[] r.
  - exists t; first by left.
    by rewrite pt.
  by case: (ih ps r) => y Y Z; exists y; first right.
Qed.

Lemma align_bind ii a p1 l :
  (let: (lbl, lc) := align ii a p1 in (lbl, lc ++ l)) =
  align ii a (let: (lbl, lc) := p1 in (lbl, lc ++ l)).
Proof. by case: p1 a => lbl lc []. Qed.

Section CAT.

Context (p:sprog) (extra_free_registers: instr_info -> option var).

Let linear_i := linear_i p extra_free_registers.

  Let Pi (i:instr) :=
    forall fn lbl tail,
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).

  Let Pr (i:instr_r) :=
    forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall fn lbl tail,
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).

  Let Pf (fd:fundef) := True.

  Let HmkI: forall i ii, Pr i -> Pi (MkI ii i).
  Proof. by []. Qed.

  Let Hskip : Pc [::].
  Proof. by []. Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc fn lbl l /=.
    by rewrite Hc; case: linear_c => lbl1 lc1; rewrite Hi (Hi _ lbl1 lc1); case: linear_i => ??; rewrite catA.
  Qed.

  Let Hassgn : forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof. by move => x tg [] // sz e ii lbl c /=; case: assert. Qed.

  Let Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by []. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii fn lbl l /=.
    case Heq1: (c1)=> [|i1 l1].
    + by rewrite Hc2 (Hc2 _ _ [:: _]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq1=> {Heq1 i1 l1};case Heq2: (c2)=> [|i2 l2].
    + by rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq2=> {Heq2 i2 l2}.
    rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1.
    rewrite Hc2 (Hc2 _ _ [::_ & _]); case: linear_c => lbl2 lc2.
    by rewrite /= !cats1 /= -!cat_rcons catA.
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Let Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii fn lbl l /=.
    case: is_bool => [ [] | ].
    + rewrite Hc' (Hc' _ _ [:: _]) align_bind; f_equal; case: linear_c => lbl1 lc1.
      by rewrite Hc (Hc _ _ (_ ++ _)); case: linear_c => lbl2 lc2; rewrite !catA cats1 -cat_rcons.
    + by apply Hc.
    case: c' Hc' => [ _ | i c' ].
    + by rewrite Hc (Hc _ _ [:: _]) align_bind; case: linear_c => lbl1 lc1; rewrite /= cats1 cat_rcons.
    move: (i :: c') => { i c' } c' Hc'.
    rewrite Hc (Hc _ _ [:: _]); case: linear_c => lbl1 lc1.
    rewrite Hc' (Hc' _ _ (_ :: _)); case: linear_c => lbl2 lc2.
    rewrite /=. f_equal. f_equal.
    by case: a; rewrite /= cats1 -catA /= cat_rcons.
  Qed.

  Let Hcall : forall i xs f es, Pr (Ccall i xs f es).
  Proof.
    move => ini xs fn es ii fn' lbl tail /=.
    case: get_fundef => // fd; case: ifP => //.
    case: sf_return_address => // [ ra | ra_ofs ] _; first by rewrite cats0 -catA.
    case: extra_free_registers => // ra.
    by rewrite cats0 -catA.
  Qed.

  Lemma linear_i_nil fn i lbl tail :
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).
  Proof.
    apply (@instr_Rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_c_nil fn c lbl tail :
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).
  Proof.
    apply (@cmd_rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

End CAT.

(* Predicate describing valid labels occurring inside instructions:
    “valid_labels fn lo hi i” expresses that labels in instruction “i” are within the range [lo; hi[
    and that remote labels to a function other than “fn” are always 1.
*)
Definition valid_labels (fn: funname) (lo hi: label) (i: linstr) : bool :=
  match li_i i with
  | Lopn _ _ _
  | Lalign
  | Ligoto _
    => true
  | Llabel lbl
  | LstoreLabel _ lbl
  | Lcond _ lbl
    => (lo <=? lbl) && (lbl <? hi)
  | Lgoto (fn', lbl) =>
    if fn' == fn then (lo <=? lbl) && (lbl <? hi) else lbl == 1
  end%positive.

Definition valid (fn: funname) (lo hi: label) (lc: lcmd) : bool :=
  all (valid_labels fn lo hi) lc.

Lemma valid_cat fn min max lc1 lc2 :
  valid fn min max (lc1 ++ lc2) = valid fn min max lc1 && valid fn min max lc2.
Proof. exact: all_cat. Qed.

Lemma valid_add_align fn lbl1 lbl2 ii a c :
  valid fn lbl1 lbl2 (add_align ii a c) = valid fn lbl1 lbl2 c.
Proof. by case: a. Qed.

Lemma valid_le_min min2 fn min1 max lc :
  (min1 <=? min2)%positive ->
  valid fn min2 max lc ->
  valid fn min1 max lc.
Proof.
  move => /Pos_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  2: case: ifP => // _.
  all: by case/andP => /h ->.
Qed.

Lemma valid_le_max max1 fn max2 min lc :
  (max1 <=? max2)%positive ->
  valid fn min max1 lc ->
  valid fn min max2 lc.
Proof.
  move => /Pos_lt_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  2: case: ifP => // _.
  all: by case/andP => -> /h.
Qed.

Lemma le_next lbl : (lbl <=? next_lbl lbl)%positive.
Proof.
  by apply Pos.leb_le; have: (Zpos lbl <= Zpos lbl + 1)%Z by lia.
Qed.

Lemma lt_next lbl : (lbl <? next_lbl lbl)%positive.
Proof.
  by apply Pos.ltb_lt; have: (Zpos lbl < Zpos lbl + 1)%Z by lia.
Qed.

Lemma find_label_cat_tl c2 c1 lbl p:
  find_label lbl c1 = ok p -> find_label lbl (c1++c2) = ok p.
Proof.
  rewrite /find_label;case:ifPn => // Hs [<-].
  by rewrite find_cat size_cat has_find Hs (ltn_addr _ Hs).
Qed.

Lemma find_labelE lbl c :
  find_label lbl c =
  if c is i :: c'
  then
    if is_label lbl i
    then ok O
    else Let r := find_label lbl c' in ok r.+1
  else type_error.
Proof.
  case: c => // i c; rewrite /find_label /=.
  case: (is_label lbl i) => //.
  rewrite ltnS.
  by case: ifP.
Qed.

(*
>>>>>>> glob_array3
Lemma find_instr_cat_tl c fn s i :
  find_instr s = Some i ->
  find_instr (setc s fn (lc s ++ c)) = Some i.
Proof.
  move => /(oseq.onthP i) /andP [Hs Hnth].
  by apply /(oseq.onthP i);rewrite size_cat nth_cat Hs (ltn_addr _ Hs).
Qed.
*)

Lemma to_estate_setc s fn : to_estate (setc s fn) = to_estate s.
Proof. by case: s. Qed.

(*
Lemma lsem_cat_tl c2 p s1 s2 :
  lsem p s1 s2 →
  lsem p
       (setc s1 s1.(lfn) (s1.(lc)++c2))
       (setc s2 s2.(lfn) (if s1.(lfn) == s2.(lfn) then s2.(lc) ++ c2  else s2.(lc))).
Proof.
  move=> H; elim H using lsem_ind; clear.
  + move => s; rewrite eqxx; once (econstructor; fail).
  rewrite /lsem1 /step /eval_instr => s1 s2 s3.
  case Heq: find_instr => [ i | // ].
  move: Heq => /find_instr_cat_tl - /(_ c2 s1.(lfn)).
  move => X Y _ Z.
  apply: lsem_step.
  move=> s1 s2 s3.
  apply: lsem_step.
  move: Hsem1;rewrite /lsem1 /step.
  case Heq : find_instr => [i |//].
  rewrite (find_instr_cat_tl c2 _ Heq) /eval_instr => {Heq}; case: i => [ii [lv o e | | l | [fn l] | e | lv l |e l]] /=;
    rewrite ?to_estate_setc;t_xrbindP.
  + by move=> [m vm] /= -> <- /=;case: s1.
  + by move=> <-;case:s1.
  + by move=> <-;case:s1.
  + case: get_fundef => // fd; case: find_label => //= lbl [<-].
    rewrite /=.

    f_equal.
    rewrite /setcpc /setc /=.
    f_equal.

    case: s1 => //.
    apply bind_eq.
  + by move=> y /(find_label_cat_tl c2) -> <- /=;case:s1.
  move=> b vb -> /= -> /=;case:b.
  + by t_xrbindP => pc /(find_label_cat_tl c2) -> <- /=;case:s1.
  by move=> [<-];case:s1.
Qed.
*)

(* FIXME
Definition is_jump (lbl: label) (i: linstr) :=
 let: MkLI ii ir := i in
 match ir with
 | Lgoto lbl' => lbl == lbl'
 | Lcond _ lbl' => lbl == lbl'
 | _ => false
end.
*)

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2) =
  (Let pc := find_label lbl c2 in ok (size c1 + pc)).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

(** Disjoint labels: all labels in “c” are below “lo” or above “hi”. *)
Definition disjoint_labels (lo hi: label) (c: lcmd) : Prop :=
  ∀ lbl, (lo <= lbl < hi)%positive → ~~ has (is_label lbl) c.

Arguments disjoint_labels _%positive _%positive _.

Lemma disjoint_labels_cat lo hi P Q :
  disjoint_labels lo hi P →
  disjoint_labels lo hi Q →
  disjoint_labels lo hi (P ++ Q).
Proof.
  by move => p q lbl r; rewrite has_cat negb_or (p _ r) (q _ r).
Qed.

Lemma disjoint_labels_w lo' hi' lo hi P :
  (lo' <= lo)%positive →
  (hi <= hi')%positive →
  disjoint_labels lo' hi' P →
  disjoint_labels lo hi P.
Proof. move => L H k lbl ?; apply: k; lia. Qed.

Lemma disjoint_labels_wL lo' lo hi P :
  (lo' <= lo)%positive →
  disjoint_labels lo' hi P →
  disjoint_labels lo hi P.
Proof. move => L; apply: (disjoint_labels_w L); lia. Qed.

Lemma disjoint_labels_wH hi' lo hi P :
  (hi <= hi')%positive →
  disjoint_labels lo hi' P →
  disjoint_labels lo hi P.
Proof. move => H; apply: (disjoint_labels_w _ H); lia. Qed.

Lemma valid_disjoint_labels fn A B C D P :
  valid fn A B P →
  (D <= A)%positive ∨ (B <= C)%positive →
  disjoint_labels C D P.
Proof.
  move => V U lbl [L H]; apply/negP => K.
  have {V K} [i _ /andP[] ] := all_has V K.
  case: i => ii [] // lbl' /andP[] /Pos.leb_le a /Pos.ltb_lt b /eqP ?; subst lbl'.
  lia.
Qed.

Lemma valid_has_not_label fn A B P lbl :
  valid fn A B P →
  (lbl < A ∨ B <= lbl)%positive →
  ~~ has (is_label lbl) P.
Proof.
  move => /(valid_disjoint_labels) - /(_ lbl (lbl + 1)%positive) V R; apply: V; lia.
Qed.

(* FIXME
Definition disjoint_lbl c1 c2 :=
  forall lbl, ~~(has (is_label lbl) c1 && has (is_jump lbl) c2).

Lemma disjoint_lbl_cons i c1 c2:
  disjoint_lbl c1 (i :: c2) -> disjoint_lbl c1 c2.
Proof.
  by move=> Hd lbl;apply: contra (Hd lbl)=> /= /andP[]->->;rewrite orbC.
Qed.

*)
(*
Definition add_hd_c c s := {| lmem := lmem s; lvm := lvm s; lfn := lfn s; lc := c ++ s.(lc); lpc := size c + s.(lpc) |}.
*)

(* This lemma is wrong: code is not preserved when calling a function
Lemma lsem1_lc p s1 s2: lsem1 p s1 s2 -> lc s1 = lc s2.
Proof.
  rewrite /lsem1 /step;case: find_instr => // -[ii [lv o e | | l | [fn l] | e | lv l | e l]] /=;
    rewrite /eval_instr /=;t_xrbindP.
  + by move=> ?? <-.
  + by move=> <-.
  + by move=> <-.
  + case: get_fundef => // fd; case: find_label => //= lbl [<-] /=.
  + by move=> ?? <-.
  move=> ????;case:ifP => [ ? | ? [<-] //].
  by t_xrbindP => ?? <-.
Qed.
*)

(*
Lemma find_instr_add_hd_c c s : find_instr (add_hd_c c s) = find_instr s.
Proof.
  rewrite /find_instr /add_hd_c /= !oseq.onth_nth map_cat nth_cat size_map.
  rewrite ltnNge leq_addr /=;f_equal;rewrite -minusE -plusE; omega.
Qed.

Lemma to_estate_add_hd_c c s : to_estate (add_hd_c c s) = to_estate s.
Proof. by case: s. Qed.
*)

(*
Lemma find_instr_has (p:linstr->bool) s i :
  find_instr s = Some i -> p i -> has p (lc s).
Proof.
  rewrite /find_instr => /(oseq.onthP i) => /andP [H1 /eqP <-] Hp.
  apply /(has_nthP i);eauto.
Qed.
*)

(* FIXME
Lemma lsem_cat_hd c s1 s2 :
  disjoint_lbl c s1.(lc) ->
  lsem s1 s2 ->
  lsem (add_hd_c c s1) (add_hd_c c s2).
Proof.
  move=> Hdisj Hsem; revert Hdisj.
  elim/lsem_ind: Hsem; clear.
  + by move=> s1 Hdisjc; apply: rt_refl.
  move=> s1 s2 s3 Hsem1 _ Hrec Hdisj.
  move: Hrec;rewrite -(lsem1_lc Hsem1) => /(_ Hdisj); apply: lsem_step.
  move: Hsem1;rewrite /lsem1 /step.
  have Hnext : forall s s1,
    of_estate s (c ++ lc s1) (size c + lpc s1).+1 = add_hd_c c (of_estate s (lc s1) (lpc s1).+1).
  + by move=> s [????];rewrite /of_estate /add_hd_c /= addnS.
  have Hset : forall pc s1,
    setpc (add_hd_c c s1) (size c + pc).+1 = add_hd_c c (setpc s1 pc.+1).
  + by move=> pc [????];rewrite /setpc /add_hd_c /= addnS.
  rewrite find_instr_add_hd_c;case Heq:find_instr => [ [ii [lv o e||l|l|e l]] | //];
    rewrite /eval_instr /= ?to_estate_add_hd_c;t_xrbindP.
  + by move=> ? -> <- /=;rewrite Hnext.
  + by move=> <-;rewrite Hset.
  + by move=> <-;rewrite Hset.
  + move=> pc' Hfind <-.
    rewrite find_label_cat_hd ?Hfind /= ? Hset //.
    by move: (Hdisj l);rewrite /disjoint_lbl (@find_instr_has (is_jump l) _ _ Heq) ?andbT /is_jump.
  move=> b vb -> /= -> /=;case:ifPn => Hb.
  + t_xrbindP => ? Hfind <-.
    rewrite find_label_cat_hd ?Hfind /= ? Hset //.
    by move: (Hdisj l);rewrite /disjoint_lbl (@find_instr_has (is_jump l) _ _ Heq) ?andbT /is_jump.
  by move=> [<-];rewrite Hset.
Qed.

Lemma valid_has c lbl p1 p2 :
  valid p1 p2 c -> has (is_label lbl) c || has (is_jump lbl) c ->
  ((p1 <=? lbl) && (lbl <? p2))%positive.
Proof.
  elim: c => //= i c Hrec /andP[] H /Hrec.
  by case: i H=>[ii [||lbl'|lbl'|e lbl']] //=;
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
*)

Definition LSem_step p s1 s2 : lsem1 p s1 s2 -> lsem p s1 s2 := rt_step _ _ s1 s2.

Lemma snot_spec gd s e b :
  sem_pexpr gd s e = ok (Vbool b) →
  sem_pexpr gd s (snot e) = sem_pexpr gd s (Papp1 Onot e).
Proof.
elim: e b => //.
- by case => // e _ b; rewrite /= /sem_sop1 /=; t_xrbindP => z -> b' /to_boolI -> _ /=;
  rewrite negbK.
- by case => // e1 He1 e2 He2 b /=; t_xrbindP => v1 h1 v2 h2 /sem_sop2I [b1 [b2 [b3]]] []
  /to_boolI hb1 /to_boolI hb2 [?] ?; subst v1 v2 b3;
  rewrite /= (He1 _ h1) (He2 _ h2) /= h1 h2;
  apply: (f_equal (@Ok _ _)); rewrite /= ?negb_and ?negb_or.
move => st p hp e1 he1 e2 he2 b /=.
t_xrbindP => bp vp -> /= -> trv1 v1 h1 htr1 trv2 v2 h2 htr2 /= h.
have : exists (b1 b2:bool), st = sbool /\ sem_pexpr gd s e1 = ok (Vbool b1) /\ sem_pexpr gd s e2 = ok (Vbool b2).
+ rewrite h1 h2;case: bp h => ?;subst.
  + have [??]:= truncate_val_boolI htr1;subst st v1.
    by move: htr2; rewrite /truncate_val; t_xrbindP => /= b2 /to_boolI -> ?;eauto.
  have [??]:= truncate_val_boolI htr2;subst st v2.
  by move: htr1; rewrite /truncate_val; t_xrbindP => /= b1 /to_boolI -> ?;eauto.
move=> [b1 [b2 [-> []/dup[]hb1 /he1 -> /dup[]hb2 /he2 ->]]] /=.
by rewrite hb1 hb2 /=; case bp.
Qed.

(* FIXME
Lemma lsem_add_align s c ii a s' :
  lsem (of_estate s c 0) (of_estate s' c (size c)) ->
  lsem (of_estate s (add_align ii a c) 0) (of_estate s' (add_align ii a c) (size (add_align ii a c))).
Proof.
  rewrite /add_align;case: a s s' => -[] m vm [] m' vm' h //.
  apply (lsem_step  (s2:=(of_estate {| emem := m; evm := vm |} ({| li_ii := ii; li_i := Lalign |} :: c) 1))); first by constructor.
  by apply: (lsem_cat_hd (c:=[::{| li_ii := ii; li_i := Lalign |}]) _ h).
Qed.
*)

Lemma add_align_nil ii a c : add_align ii a c = add_align ii a [::] ++ c.
Proof. by case: a. Qed.

Lemma find_label_add_align lbl ii a c :
  find_label lbl (add_align ii a c) =
  Let n := find_label lbl c in ok ((a == Align) + n).
Proof.
  case: a => /=;last by case: find_label.
  by rewrite /add_align -cat1s find_label_cat_hd.
Qed.

(** Technical lemma about the compilation: monotony and unicity of labels. *)
Section VALIDITY.
  Context (p: sprog) (extra_free_registers: instr_info → option var) (lp: lprog).

  Let Pr (i: instr_r) : Prop :=
    ∀ ii fn lbl,
      let: (lbli, li) := linear_i p extra_free_registers fn (MkI ii i) lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pi (i: instr) : Prop :=
    ∀ fn lbl,
      let: (lbli, li) := linear_i p extra_free_registers fn i lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pc (c: cmd) : Prop :=
    ∀ fn lbl,
      let: (lblc, lc) := linear_c (linear_i p extra_free_registers fn) c lbl [::] in
      (lbl <= lblc)%positive ∧ valid fn lbl lblc lc.

  Let HMkI i ii : Pr i → Pi (MkI ii i).
  Proof. exact. Qed.

  Let Hnil : Pc [::].
  Proof. move => fn lbl /=; split => //; lia. Qed.

  Let Hcons (i : instr) (c : cmd) : Pi i → Pc c → Pc (i :: c).
  Proof.
    move => hi hc fn lbl /=.
    case: linear_c (hc fn lbl) => lblc lc [Lc Vc]; rewrite linear_i_nil.
    case: linear_i (hi fn lblc) => lbli li [Li Vi]; split; first lia.
    rewrite valid_cat; apply/andP; split.
    - apply: valid_le_min _ Vi; apply/Pos.leb_le; lia.
    apply: valid_le_max _ Vc; apply/Pos.leb_le; lia.
  Qed.

  Let Hassign (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) : Pr (Cassgn x tg ty e).
  Proof. move => ii fn lbl /=; case: ty; split => //; exact: Pos.le_refl. Qed.

  Let Hopn (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs) : Pr (Copn xs t o es).
  Proof. split => //; exact: Pos.le_refl. Qed.

  Let Hif (e : pexpr) (c1 c2 : cmd) : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
  Proof.
    move => hc1 hc2 ii fn lbl /=.
    case: c1 hc1 => [ | i1 c1 ] hc1.
    - rewrite linear_c_nil.
      case: linear_c (hc2 fn (next_lbl lbl)); rewrite /next_lbl => lblc2 lc2 [L2 V2]; split; first lia.
      have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc2 /= andbT.
      apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    case: c2 hc2 => [ | i2 c2 ] hc2.
    - rewrite linear_c_nil.
      case: linear_c (hc1 fn (next_lbl lbl)); rewrite /next_lbl => lblc1 lc1 [L1 V1]; split; first lia.
      have lbl_lt_lblc1 : (lbl <? lblc1)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc1 /= andbT.
      apply: valid_le_min _ V1; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc1 fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc1 lc1 [L1 V1].
    rewrite linear_c_nil.
    case: linear_c (hc2 fn lblc1) => lblc2 lc2 [L2 V2]; split; first lia.
    have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lblp1_lt_lblc2 : (lbl + 1 <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    rewrite /= valid_cat /= valid_cat /= /valid_labels /= Pos.leb_refl /= eqxx lbl_lt_lblc2 lblp1_lt_lblc2 lbl_le_lblp1 /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ V1.
    all: apply/Pos.leb_le; lia.
  Qed.

  Let Hfor (v : var_i) (d: dir) (lo hi : pexpr) (c : cmd) : Pc c → Pr (Cfor v (d, lo, hi) c).
  Proof. split => //; exact: Pos.le_refl. Qed.

  Let Hwhile (a : expr.align) (c : cmd) (e : pexpr) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {e} e ].
    - rewrite linear_c_nil.
      case: linear_c (hc' fn (next_lbl lbl)); rewrite /next_lbl => lblc' lc' [Lc' Vc'].
      rewrite linear_c_nil.
      case: linear_c (hc fn lblc') => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= !valid_cat /= /valid_labels /= Pos.leb_refl eqxx lbl_lt_lblc /= andbT.
      apply/andP; split.
      - apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
      apply: valid_le_max; last apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    - by case: linear_c (hc fn lbl).
    case: c' hc' => [ | i' c' ] hc'.
    - rewrite linear_c_nil.
      case: linear_c (hc fn (next_lbl lbl)); rewrite /next_lbl => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= valid_cat /= /valid_labels /= Pos.leb_refl lbl_lt_lblc /= andbT.
      apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc lc [Lc Vc].
    rewrite linear_c_nil.
    case: linear_c (hc' fn lblc) => lblc' lc' [Lc' Vc'] /=; split; first lia.
    have lbl_lt_lblc' : (lbl <? lblc')%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    have lblp1_lt_lblc' : (lbl + 1 <? lblc')%positive by apply/Pos.ltb_lt; lia.
    rewrite valid_add_align /= valid_cat /= valid_cat /= /valid_labels /= eqxx Pos.leb_refl lbl_lt_lblc' lbl_le_lblp1 lblp1_lt_lblc' /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ Vc.
    all: apply/Pos.leb_le; lia.
  Qed.

  Remark valid_allocate_stack_frame fn lbl b ii z :
    valid fn lbl (lbl + 1)%positive (allocate_stack_frame b ii z).
  Proof. by rewrite /allocate_stack_frame; case: eqP. Qed.

  Let Hcall (i : inline_info) (xs : lvals) (f : funname) (es : pexprs) : Pr (Ccall i xs f es).
  Proof.
    move => ii fn lbl /=.
    case: get_fundef => [ fd | ]; last by split => //; lia.
    case: eqP; first by split => //; lia.
    have lbl_lt_lblp1 : (lbl <? lbl + 1)%positive by apply/Pos.ltb_lt; lia.
    case: sf_return_address => // ra _.
    - rewrite /next_lbl; split; first lia.
      rewrite valid_cat /= valid_cat /= !valid_allocate_stack_frame /= /valid_labels /= Pos.leb_refl lbl_lt_lblp1 /= andbT.
      by case: eqP => _ //; rewrite Pos.leb_refl lbl_lt_lblp1.
    rewrite /next_lbl; case: extra_free_registers => [ ra' | ] ; last by split => //; lia.
    split; first lia.
    rewrite valid_cat /= valid_cat !valid_allocate_stack_frame /= /valid_labels /= Pos.leb_refl lbl_lt_lblp1 /= andbT.
    by case: eqP => _ //; rewrite Pos.leb_refl lbl_lt_lblp1.
  Qed.

  Definition linear_has_valid_labels : ∀ c, Pc c :=
    @cmd_rect Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hif Hfor Hwhile Hcall.

  Definition linear_has_valid_labels_instr : ∀ i, Pi i :=
    @instr_Rect Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hif Hfor Hwhile Hcall.

End VALIDITY.

Section PROOF.

  Variable p:  sprog.
  Variable extra_free_registers: instr_info -> option var.
  Variable p': lprog.

  Hypothesis linear_ok : linear_prog p extra_free_registers = ok p'.

  Notation linear_i := (linear_i p extra_free_registers).
  Notation linear_c fn := (linear_c (linear_i fn)).

  Notation sem_I := (sem_one_varmap.sem_I p extra_free_registers).
  Notation sem_i := (sem_one_varmap.sem_i p extra_free_registers).
  Notation sem := (sem_one_varmap.sem p extra_free_registers).

  Notation valid_c fn c := (linear_has_valid_labels p extra_free_registers c fn).
  Notation valid_i fn i := (linear_has_valid_labels_instr p extra_free_registers i fn).

  Definition checked_i fn i : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_i p extra_free_registers fn fd.(f_extra).(sf_align) i is Ok tt
      then true
      else false
    else false.

  Lemma checked_iE fn i :
    checked_i fn i →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_i p extra_free_registers fn fd.(f_extra).(sf_align) i = ok tt.
    Proof.
      rewrite /checked_i; case: get_fundef => // fd h; exists fd; first by [].
      by case: check_i h => // - [].
    Qed.

  Definition checked_c fn c : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_c (check_i p extra_free_registers fn fd.(f_extra).(sf_align)) c is Ok tt
      then true
      else false
    else false.

  Lemma checked_cE fn c :
    checked_c fn c →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_c (check_i p extra_free_registers fn fd.(f_extra).(sf_align)) c = ok tt.
    Proof.
      rewrite /checked_c; case: get_fundef => // fd h; exists fd; first by [].
      by case: check_c h => // - [].
    Qed.

    Lemma checked_cI fn i c :
      checked_c fn (i :: c) →
      checked_i fn i ∧ checked_c fn c.
    Proof.
      by case/checked_cE => fd ok_fd; rewrite /checked_c /checked_i ok_fd /= ; t_xrbindP => - [] -> ->.
    Qed.

  Local Lemma p_globs_nil : p_globs p = [::].
  Proof.
    by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ /assertP /eqP /size0nil.
  Qed.

  Local Lemma checked_prog fn fd :
    get_fundef (p_funcs p) fn = Some fd →
    check_fd p extra_free_registers (fn, fd) = ok tt.
  Proof.
    move: linear_ok; rewrite /linear_prog; apply: rbindP => - [] ok_p _ /(@get_fundef_in' _ _ _ _).
    move: ok_p; rewrite /check_prog; apply: rbindP => r C _ M.
    by have [ [] [] ] := mapM_In C M.
  Qed.

  Lemma get_fundef_p' f fd :
    get_fundef (p_funcs p) f = Some fd →
    get_fundef (lp_funcs p') f = Some (linear_fd p extra_free_registers f fd).
  Proof.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ _ <- /=.
    by rewrite /get_fundef assoc_map2 => ->.
  Qed.

  Local Coercion emem : estate >-> mem.
  Local Coercion evm : estate >-> vmap.

  (** Relation between source and target memories
      - There is a well-aligned valid block in the target
   *)
  Record match_mem (m m': mem) : Prop :=
    MM {
       read_incl  : ∀ p w, read m p U8 = ok w → read m' p U8 = ok w
     ; valid_incl : ∀ p, validw m p U8 → validw m' p U8
     ; valid_stk  : ∀ p, 
         (wunsigned (stack_limit m) <= wunsigned p < wunsigned(stack_root m))%Z
       → validw m' p U8
      }.
   
  Lemma mm_free : ∀ m1 m1',
  match_mem m1 m1' →
  match_mem (free_stack m1) m1'.
  Proof.
  move=> m1 m1' [] Hrm Hvm Hsm. constructor.
  (* read *)
  + move=> p1 w1 Hr. have Hv := (readV Hr).
    have Hs := free_stackP. move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
    apply Hrm. rewrite -Hr. eapply fss_read_old. apply Hm1. apply Hv.
  (* valid *)
  + move=> p1 Hv. 
    have Hs := free_stackP. move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
    have Heq := (fss_valid Hm1). have Heq' := (fss_valid Hm1').
    apply Hvm. rewrite Heq in Hv. move: Hv. move=>/andP [] Hv1 Hv2.
    apply Hv1.
  (* stack *)
  have Hs := free_stackP. move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
  have Heq := (fss_valid Hm1).
  move=> p1 Hs'. apply Hsm. have <- := fss_root Hm1. by have <- := fss_limit Hm1. 
  Qed.

  Lemma mm_read_ok : ∀ m m' a s v,
  match_mem m m' →
  read m a s = ok v →
  read m' a s = ok v.
  Proof.
  move=> m m' p'' s v [] Hrm Hvm Hsm Hr.
  have := read_read8 Hr. move=> [] Ha Hi.
  have : validw m' p'' s. apply /validwP.
  split=>//. move=> i Hi'. apply Hvm. move: (Hi i Hi')=> Hr'.
  by have Hv := readV Hr'. move=> Hv. rewrite -Hr.
  apply eq_read. move=> i Hi'. move: (Hi i Hi')=> Hr'.
  move: (Hrm (add p'' i) (LE.wread8 v i) Hr'). move=> Hr''.
  by rewrite Hr' Hr''.
  Qed.
  
   Lemma mm_write : ∀ m1 m1' p s (w:word s) m2,
   match_mem m1 m1' →
   write m1 p w = ok m2 →
   exists2 m2', write m1' p w = ok m2' & match_mem m2 m2'.
   Proof.
   move=> m1 m1' p'' sz w m2 Hm Hw.
   case: Hm=> H1 H2 H3. have /validwP := (write_validw Hw).
   move=> [] Ha Hi.
   have /writeV : validw m1' p'' sz. apply /validwP. split=> //. move=> i Hi'.
   move: (Hi i Hi')=> Hv. by move: (H2 (add p'' i) Hv). move=> Hw'.
   move: (Hw' w). move=> [] m2' Hw''. exists m2'.
   + by apply Hw''.
   constructor.
   (* read *)
   + move=> p1 w1 Hr1. admit.
   (* valid *)
   + move=> p1 Hv. have Hv1 := (CoreMem.write_validw p1 U8 Hw).
     have Hv2 := (CoreMem.write_validw p1 U8 Hw''). rewrite Hv2.
     apply H2. by rewrite -Hv1.
   (* stack *)
   move=> p1 H. have Hv1 := (CoreMem.write_validw p1 U8 Hw).
   have Hv2 := (CoreMem.write_validw p1 U8 Hw''). rewrite Hv2.
   apply H3. admit.
   Admitted.

  Lemma mm_alloc : ∀ m1 m1' al sz es' m2,
  match_mem m1 m1' →
  alloc_stack m1 al sz es' = ok m2 →
  match_mem m2 m1'.
  Proof.
  move=> m1 m1' sz sz' z m2 [] Hvm Hrm Hs Ha.
  have := alloc_stackP Ha. move=> [] Hvr Hve Hveq {Ha} Ha Hs' Hs'' Hsr Hsl Hf.
  constructor.
  (* read *)
  + move=> p1 w1 Hr1. case Heq: (validw m1 p1 U8)=> //.
    + move: (Hvr p1 Heq)=> {Hvr} Hvr. move: (Hvm p1)=> {Hvm} Hvm. 
      rewrite Hvr in Hvm. by apply Hvm.
    move: (Hveq p1)=> {Hveq} Hveq. rewrite Heq /= in Hveq. 
    apply Hvm. move: (Hve p1). unfold not. move=> {Hve} Hve.
    rewrite Heq in Hve. have H : false-> False. move=> hf. inversion hf.
    move: (Hve H)=> {Hve} Hve. rewrite Hr1 in Hve. rewrite Hveq in Hve.
    admit.
  (* valid *)
  + move=> p1 Hv1. apply Hrm. move: (Hveq p1)=> {Hveq} Hveq.
    admit.
  (* stack *)
  move=> p1 Hs'''. apply Hs. by rewrite -Hsr -Hsl.
  Admitted.

  Lemma mm_write_invalid : ∀ m m1' p s (w: word s),
  match_mem m m1' →
  (wunsigned (stack_limit m) <= wunsigned p ∧ wunsigned p + wsize_size s <= wunsigned (top_stack m))%Z →
  exists2 m2', write m1' p w = ok m2' & match_mem m m2'.
  Proof.
  move=> m m1' p1 sz w [] Hrm Hvm Hs Hs'.
  apply mm_write with m. constructor.
  apply Hrm. apply Hvm. apply Hs.
  (* can it be same memory after writting at a location? *)
  move: (Hs p1)=> {Hs} Hs. 
  Admitted.


  Section MATCH_MEM_SEM_PEXPR.
    Context (m m': mem) (vm: vmap) (M: match_mem m m').
    Let P (e: pexpr) : Prop :=
      ∀ v,
        sem_pexpr [::] {| emem := m ; evm := vm |} e = ok v →
        sem_pexpr [::] {| emem := m' ; evm := vm |} e = ok v.

    Let Q (es: pexprs) : Prop :=
      ∀ vs,
        sem_pexprs [::] {| emem := m ; evm := vm |} es = ok vs →
        sem_pexprs [::] {| emem := m' ; evm := vm |} es = ok vs.

    Lemma match_mem_sem_pexpr_pair : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split.
      - by [].
      - by move => e ihe es ihes vs /=; t_xrbindP => ? /ihe -> /= ? /ihes -> /= ->.
      1-4: by rewrite /P /=.
      - move => aa sz x e ihe vs /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - move => aa sz len x e ihe v /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - by move => sz x e ihe v /=; t_xrbindP => ?? -> /= -> /= ?? /ihe -> /= -> /= ? /(mm_read_ok M) -> /= ->.
      - by move => op e ihe v /=; t_xrbindP => ? /ihe ->.
      - by move => op e1 ih1 e2 ih2 v /=; t_xrbindP => ? /ih1 -> ? /ih2 ->.
      - by move => op es ih vs /=; t_xrbindP => ? /ih; rewrite -/(sem_pexprs [::] _ es) => ->.
      by move => ty e ihe e1 ih1 e2 ih2 v /=; t_xrbindP => ?? /ihe -> /= -> ?? /ih1 -> /= -> ?? /ih2 -> /= -> /= ->.
    Qed.

  Lemma match_mem_sem_pexpr e : P e.
  Proof. exact: (proj1 match_mem_sem_pexpr_pair). Qed.

  Lemma match_mem_sem_pexprs es : Q es.
  Proof. exact: (proj2 match_mem_sem_pexpr_pair). Qed.

  End MATCH_MEM_SEM_PEXPR.

  Lemma match_mem_write_lval m1 vm1 m1' m2 vm2 x v :
    match_mem m1 m1' →
    write_lval [::] x v {| emem := m1 ; evm := vm1 |} = ok {| emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lval [::] x v {| emem := m1' ; evm := vm1 |} = ok {| emem := m2' ; evm := vm2 |} &
    match_mem m2 m2'.
  Proof.
    move => M; case: x => /= [ _ ty | x | ws x e | aa ws x e | aa ws n x e ].
    - case/write_noneP => - [] -> -> h; exists m1'; last exact: M.
      rewrite /write_none.
      by case: h => [ [u ->] | [ -> -> ] ].
    - rewrite /write_var /=; t_xrbindP =>_ -> <- -> /=.
      by exists m1'.
    - t_xrbindP => ?? -> /= -> /= ?? /(match_mem_sem_pexpr M) -> /= -> /= ? -> /= ? /(mm_write M)[] ? -> /= M' <- <-.
      eexists; first reflexivity; exact: M'.
    all: apply: on_arr_varP; t_xrbindP => ??? -> /= ?? /(match_mem_sem_pexpr M) -> /= -> /= ? -> /= ? -> /= ? -> /= <- <-.
    all: by exists m1'.
  Qed.

  Lemma match_mem_write_lvals m1 vm1 m1' m2 vm2 xs vs :
    match_mem m1 m1' →
    write_lvals [::] {| emem := m1 ; evm := vm1 |} xs vs = ok {| emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lvals [::] {| emem := m1' ; evm := vm1 |} xs vs = ok {| emem := m2' ; evm := vm2 |} &
    match_mem m2 m2'.
  Proof.
    elim: xs vs vm1 m1 m1'.
    - by case => // vm1 m1 m1' M [] <- <- {m2 vm2}; exists m1'.
    by move => x xs ih [] // v vs vm1 m1 m1' M /=; t_xrbindP => - [] ?? /(match_mem_write_lval M)[] m2' -> M2 /ih - /(_ _ M2).
  Qed.

  Definition is_linear_of (fn: funname) (c: lcmd) : Prop :=
    exists2 fd, get_fundef (lp_funcs p') fn = Some fd & fd.(lfd_body) = c.

  Definition is_ra_of (fn: funname) (ra: return_address_location) : Prop :=
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & fd.(f_extra).(sf_return_address) = ra.

  (** Export functions allocate their own stack frames
  * whereas internal functions have their frame allocated by the caller *)
  Definition is_sp_for_call (fn: funname) (m: mem) (ptr: pointer) : Prop :=
    exists2 fd,
    get_fundef (p_funcs p) fn = Some fd &
    let e := fd.(f_extra) in
    if e.(sf_return_address) is RAnone
    then ptr = top_stack m
    else
      is_align (top_stack m) e.(sf_align) ∧
      let sz := stack_frame_allocation_size e in ptr = (top_stack m - wrepr Uptr sz)%R.

  Definition value_of_ra (m: mem) (vm: vmap) (ra: return_address_location) (target: option (remote_label * lcmd * nat)) : Prop :=
    match ra, target with
    | RAnone, None => True
    | RAreg (Var sword64 _ as ra), Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc &
          exists2 ptr, encode_label (label_in_lprog p') (caller, lbl) = Some ptr & vm.[ra] = ok (pword_of_word ptr)
      ]
    | RAstack ofs, Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc &
          exists2 ptr, encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
          exists2 sp, vm.[ var_of_register RSP ] = ok (pword_of_word sp) & read m (sp + wrepr Uptr ofs)%R Uptr = ok ptr
      ]
    | _, _ => False
    end%vmap.

  Variant ex2_5 (T1 T2: Type) (A B C D E : T1 → T2 → Prop) : Prop :=
    Ex2_4 x1 x2 of A x1 x2 & B x1 x2 & C x1 x2 & D x1 x2 & E x1 x2.

  Let Pi (k: Sv.t) (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn i →
      let: (lbli, li) := linear_i fn i lbl [::] in
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       ex2_5
       (λ m2 vm2, lsem p' (Lstate m1 vm1 fn (size P)) (Lstate m2 vm2 fn (size (P ++ li))))
       (λ _ vm2, vm1 = vm2 [\ k ])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, match_mem s2 m2).

  Let Pi_r (ii: instr_info) (k: Sv.t) (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn (MkI ii i) →
      let: (lbli, li) := linear_i fn (MkI ii i) lbl [::] in
      (if extra_free_registers ii is Some fr then if vtype fr is sword _ then s1.[fr]%vmap = Error ErrAddrUndef else True else True) →
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       ex2_5
       (λ m2 vm2, lsem p' (Lstate m1 vm1 fn (size P)) (Lstate m2 vm2 fn (size (P ++ li))))
       (λ _ vm2, vm1 = vm2 [\ Sv.union k (extra_free_registers_at extra_free_registers ii)])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, match_mem s2 m2).

  Let Pc (k: Sv.t) (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_c fn c →
      let: (lblc, lc) := linear_c fn c lbl [::] in
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lblc P →
       is_linear_of fn (P ++ lc ++ Q) →
       ex2_5
       (λ m2 vm2, lsem p' (Lstate m1 vm1 fn (size P)) (Lstate m2 vm2 fn (size (P ++ lc))))
       (λ _ vm2, vm1 = vm2 [\ k ])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, match_mem s2 m2).

  Let Pfun (ii: instr_info) (k: Sv.t) (s1: estate) (fn: funname) (s2: estate) : Prop :=
    ∀ m1 vm1 body ra lret sp,
       wf_vm vm1 →
      match_mem s1 m1 →
      vm_uincl (if ra is RAreg x then s1.[x <- undef_error] else s1).[var_of_register RSP <- ok (pword_of_word sp)]%vmap vm1 →
      is_linear_of fn body →
      (* RA contains a safe return address “lret” *)
      is_ra_of fn ra →
      value_of_ra m1 vm1 ra lret →
      (* RSP points to the top of the stack according to the calling convention *)
      is_sp_for_call fn s1 sp →
      ex2_5
      (λ m2 vm2,
      if lret is Some ((caller, lbl), _cbody, pc)
      then
        lsem p' (Lstate m1 vm1 fn 1) (Lstate m2 vm2 caller pc.+1)
      else lsem p' (Lstate m1 vm1 fn 0) (Lstate m2 vm2 fn (size body)))
      (λ _ vm2, vm1 = vm2 [\ Sv.union k (extra_free_registers_at extra_free_registers ii)])
      (λ _ vm2, wf_vm vm2)
      (λ _ vm2, vm_uincl s2.[var_of_register RSP <- ok (pword_of_word sp)] vm2)
      (λ m2 _, match_mem s2 m2).

  Lemma label_in_lfundef fn body (lbl: label) :
    lbl \in label_in_lcmd body →
    is_linear_of fn body →
    (fn, lbl) \in label_in_lprog p'.
  Proof.
    clear.
    rewrite /label_in_lprog => X [] fd ok_fd ?; subst body.
    apply/flattenP => /=.
    exists [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd) ];
      last by apply/map_f: X.
    apply/in_map.
    by exists (fn, fd); first exact: get_fundef_in'.
  Qed.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move => s1 fn lbl _ m1 vm1 P Q M X D C; rewrite cats0; exists m1 vm1 => //; exact: rt_refl.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p extra_free_registers Pc Pi.
  Proof.
    move => ki kc s1 s2 s3 i c exec_i hi _ hc.
    move => fn lbl /checked_cI[] chk_i chk_c /=.
    case: (linear_c fn) (valid_c fn c lbl) (hc fn lbl chk_c) => lblc lc [Lc Vc] Sc.
    rewrite linear_i_nil.
    case: linear_i (valid_i fn i lblc) (hi fn lblc chk_i) => lbli li [Li Vi] Si.
    move => m1 vm1 P Q Wc Mc Xc Dc C.
    have D : disjoint_labels lblc lbli P.
    + apply: (disjoint_labels_wL _ Dc); exact: Lc.
    have C' : is_linear_of fn (P ++ li ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have [ m2 vm2 Ei Ki Wi Xi Mi ] := Si m1 vm1 P (lc ++ Q) Wc Mc Xc D C'.
    have Di : disjoint_labels lbl lblc (P ++ li).
    + apply: disjoint_labels_cat.
      * apply: (disjoint_labels_wH _ Dc); exact: Li.
      apply: (valid_disjoint_labels Vi); lia.
    have Ci : is_linear_of fn ((P ++ li) ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have [ m3 vm3 ] := Sc m2 vm2 (P ++ li) Q Wi Mi Xi Di Ci.
    rewrite -!catA => E K W X M.
    exists m3 vm3; [ | | exact: W | exact: X | exact: M ].
    + exact: lsem_trans Ei E.
    apply: vmap_eq_exceptT; apply: vmap_eq_exceptI.
    2: exact: Ki.
    3: exact: K.
    all: SvD.fsetdec.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p extra_free_registers Pi Pi_r.
  Proof.
    move => ii k i s1 s2 ok_fr _ h _ fn lbl chk.
    move: h => /(_ fn lbl chk); case: linear_i (valid_i fn (MkI ii i) lbl) => lbli li [L V] S.
    move => m1 vm1 P Q W M X D C.
    have E : match extra_free_registers ii return Prop with
      | Some fr => if vtype fr is sword _ then ((kill_extra_register extra_free_registers ii s1).[fr])%vmap = Error ErrAddrUndef else True
      | None => True
      end.
    - rewrite /kill_extra_register /kill_extra_register_vmap /=.
      case: extra_free_registers => // - [] [] //= sz fr.
      case h1: s1.[ Var (sword sz) fr ]%vmap => /= [ v | e ].
      + by rewrite Fv.setP_eq.
      move: (X (Var (sword sz) fr)) (W (Var (sword sz) fr)); rewrite h1 {h1} /=.
      by case: _.[_]%vmap => //=; case: e => // e <-.
    have {S E} S := S E.
    have [ | {W M X} ] := S _ vm1 _ _ W M _ D C.
    - by apply: vm_uincl_trans; first exact: kill_extra_register_vm_uincl.
    move => m2 vm2 E K W X M.
    exists m2 vm2.
    - exact: E.
    - apply: vmap_eq_exceptI K; SvD.fsetdec.
    - exact: W.
    - exact: X.
    exact: M.
  Qed.

  Lemma find_instrE fn body :
    is_linear_of fn body →
    ∀ m vm n,
    find_instr p' (Lstate m vm fn n) = oseq.onth body n.
  Proof. by rewrite /find_instr => - [] fd /= -> ->. Qed.

  Lemma find_instr_skip fn P Q :
    is_linear_of fn (P ++ Q) →
    ∀ m vm n,
    find_instr p' (Lstate m vm fn (size P + n)) = oseq.onth Q n.
  Proof.
    move => h m vm n; rewrite (find_instrE h).
    rewrite !oseq.onth_nth map_cat nth_cat size_map.
    rewrite ltnNge leq_addr /=;f_equal;rewrite -minusE -plusE; lia.
  Qed.

  Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => ii s1 s2 x tg ty e v v'; rewrite p_globs_nil => ok_v ok_v' ok_s2.
    move => fn lbl /checked_iE[] fd ok_fd.
    case: ty ok_v' ok_s2 => // sz.
    apply: rbindP => w /of_val_word [sz'] [w'] [hle ? ?]; subst v w => -[<-] {v'} ok_s2 chk.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D1 C1.
    have [ v' ok_v' ] := sem_pexpr_uincl X1 ok_v.
    case/value_uinclE => [sz''] [w] [?]; subst v' => /andP[] hle' /eqP ?; subst w'.
    rewrite (zero_extend_idem _ hle) in ok_s2.
    have [ vm2 /(match_mem_write_lval M1) [ m2 ok_s2' M2 ] ok_vm2 ] := write_uincl X1 (value_uincl_refl _) ok_s2.
    exists m2 vm2; [ | | | exact: ok_vm2 | exact: M2]; last first.
    + exact: wf_write_lval ok_s2'.
    + apply: vmap_eq_exceptI; first exact: SvP.MP.union_subset_1.
      by have := vrvP ok_s2'.
    apply: LSem_step.
    rewrite -(addn0 (size P)) /lsem1 /step /= (find_instr_skip C1) /= /eval_instr /to_estate /=.
    case: ifP => hsz.
    + rewrite /sem_sopn /sem_pexprs /= /exec_sopn /sopn_sem /=.
      rewrite (match_mem_sem_pexpr M1 ok_v') /=.
      rewrite /truncate_word (cmp_le_trans hle hle') /x86_MOV /check_size_8_64 hsz /= ok_s2' /=.
      by rewrite size_cat addn1 addn0.
    rewrite /sem_sopn /= /exec_sopn /sopn_sem /=.
    rewrite (match_mem_sem_pexpr M1 ok_v') /=.
    rewrite /truncate_word (cmp_le_trans hle hle') /= /x86_VMOVDQU
      (wsize_nle_u64_check_128_256 hsz) /= ok_s2' /=.
    by rewrite size_cat addn1 addn0.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => rs vs.
    rewrite p_globs_nil => ok_vs ok_rs ok_s2.
    move => fn lbl /checked_iE[] fd ok_fd chk.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D1 C1.
    have [ vs' /(match_mem_sem_pexprs M1) ok_vs' vs_vs' ] := sem_pexprs_uincl X1 ok_vs.
    have [ rs' [ ok_rs' rs_rs' ] ] := vuincl_exec_opn vs_vs' ok_rs.
    have [ vm2 /(match_mem_write_lvals M1) [ m2 ok_s2' M2 ] ok_vm2 ] := writes_uincl X1 rs_rs' ok_s2.
    exists m2 vm2; [ | | | exact: ok_vm2 | exact: M2 ]; last first.
    + exact: wf_write_lvals ok_s2'.
    + apply: vmap_eq_exceptI; first exact: SvP.MP.union_subset_1.
      by have := vrvsP ok_s2'.
    apply: LSem_step.
    rewrite -(addn0 (size P)) /lsem1 /step /= (find_instr_skip C1) /= /eval_instr /to_estate /=.
    by rewrite /sem_sopn ok_vs' /= ok_rs' /= ok_s2' /= size_cat addn0 addn1.
  Qed.

  Remark next_lbl_neq (lbl: label) :
    ((lbl + 1)%positive == lbl) = false.
  Proof.
    apply/eqP => k.
    suff : (lbl < lbl)%positive by lia.
    rewrite -{2}k; lia.
  Qed.

  Lemma eval_jumpE fn body :
    is_linear_of fn body →
    ∀ lbl s,
    eval_jump p' (fn, lbl) s = Let pc := find_label lbl body in ok (setcpc s fn pc.+1).
  Proof. by case => ? /= -> ->. Qed.

  Local Lemma Hif_true : sem_Ind_if_true p extra_free_registers Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E1 Hc1 fn lbl /checked_iE[] fd ok_fd /=; apply: rbindP => -[] chk_c1 _.
    case: c1 E1 Hc1 chk_c1 => [ | i1 c1 ] E1 Hc1 chk_c1; last case: c2 => [ | i2 c2 ].
    + case/semE: E1 => hk ?; subst s2.
      rewrite /= linear_c_nil; case: (linear_c fn) (valid_c fn c2 (next_lbl lbl)) => lbl2 lc2.
      rewrite /next_lbl => - [L V].
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C1.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m1 vm1; [ | | exact: W1 | exact: X1 | exact: M1 ]; last by [].
      apply: LSem_step.
      rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C1) /= /eval_instr /to_estate /li_i (eval_jumpE C1) /to_estate /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      by rewrite size_cat /= size_cat /= -addn1 -addnA.
    + rewrite linear_c_nil.
      case: (linear_c fn) (Hc1 fn (next_lbl lbl)) => lbl1 lc1.
      rewrite /checked_c ok_fd chk_c1 => /(_ erefl) S.
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C1.
      set P' := rcons P (MkLI ii (Lcond (snot e) lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl1 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Llabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc1 ++ Q').
      - by move: C1; rewrite /P' /Q' -cats1 /= -!catA.
      have {S} [ m2 vm2 E K2 W2 X2 M2 ] := S m1 vm1 P' Q' W1 M1 X1 D' C'.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
      exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: M2 ].
      apply: lsem_step; last apply: lsem_trans.
      2: exact: E.
      - by rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C1) /= /eval_instr /li_i (eval_jumpE C1) /to_estate /= (snot_spec ok_e') /= ok_e' /= /setpc /= addn0 /P' /Q' size_rcons.
      apply: LSem_step.
      rewrite catA in C'.
      rewrite /lsem1 /step -(addn0 (size (P' ++ lc1))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
      by rewrite /P' /Q' -cats1 -!catA !size_cat addn0 /= size_cat /= !addnS addn0.
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) (Hc1 fn (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite /checked_c ok_fd chk_c1 => /(_ erefl) E.
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) => lbl2 lc2 [L2 V2].
    move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
    have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set P' := P ++ {| li_ii := ii; li_i := Lcond e lbl |} :: lc2 ++ [:: {| li_ii := ii; li_i := Lgoto (fn, (lbl + 1)%positive) |}; {| li_ii := ii; li_i := Llabel lbl |} ].
    have D' : disjoint_labels (lbl + 1 + 1) lbl1 P'.
    + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
      apply: disjoint_labels_cat; first by apply: (valid_disjoint_labels V2); lia.
      move => lbl' [A B]; rewrite /= orbF /is_label /=; apply/eqP => ?; subst lbl'; lia.
    set Q' := {| li_ii := ii; li_i := Llabel (lbl + 1) |} :: Q.
    have C' : is_linear_of fn (P' ++ lc1 ++ Q').
    + by move: C; rewrite /P' /Q' /= -!catA /= -!catA.
    have {E} [ m2 vm2 E K2 W2 X2 M2 ] := E m1 vm1 P' Q' W1 M1 X1 D' C'.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
    exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: M2 ].
    apply: lsem_step; last apply: lsem_trans.
    2: exact: E.
    - rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i  (eval_jumpE C) /to_estate /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V2); lia.
      by rewrite /= find_labelE /= find_labelE /is_label /= eqxx /= /setcpc /= /P' /Q' size_cat /= size_cat /= !addnS.
    apply: LSem_step.
    rewrite catA in C'.
    rewrite /lsem1 /step -(addn0 (size (P' ++ lc1))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
    by rewrite /P' /Q' -!catA /= -!catA; repeat rewrite !size_cat /=; rewrite !addnS !addn0.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p extra_free_registers Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E2 Hc2 fn lbl /checked_iE[] fd ok_fd /=; apply: rbindP => -[] _ chk_c2.
    case: c1 => [ | i1 c1 ]; last case: c2 E2 Hc2 chk_c2 => [ | i2 c2 ].
    + rewrite linear_c_nil.
      case: (linear_c fn) (Hc2 fn (next_lbl lbl)) => lbl2 lc2.
      rewrite /checked_c ok_fd chk_c2 => /(_ erefl) S.
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
      set P' := rcons P (MkLI ii (Lcond e lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl2 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Llabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc2 ++ Q').
      - by move: C; rewrite /P' /Q' -cats1 /= -!catA.
      have {S} [ m2 vm2 E K2 W2 X2 M2 ] := S m1 vm1 P' Q' W1 M1 X1 D' C'.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
      exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: M2 ].
      apply: lsem_step; last apply: lsem_trans.
      2: exact: E.
      - by rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= ok_e' /= /setpc /= addn0 /P' /Q' size_rcons.
      apply: LSem_step.
      rewrite catA in C'.
      rewrite /lsem1 /step -(addn0 (size (P' ++ lc2))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
      by rewrite /P' /Q' -cats1 -!catA !size_cat addn0 /= size_cat /= !addnS addn0.
    + case/semE => hk ? _ _; subst s2.
      rewrite linear_c_nil; case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl lbl)) => lbl1 lc1.
      rewrite /next_lbl => - [L V].
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m1 vm1; [ | | exact: W1 | exact: X1 | exact: M1 ]; last by [].
      apply: LSem_step.
      rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= (snot_spec ok_e') /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      - apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      by rewrite size_cat /= size_cat /= -addn1 -addnA.
    rewrite linear_c_nil => _ Hc2 chk_c2.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) (Hc2 fn lbl1) => lbl2 lc2 [L2 V2].
    rewrite /checked_c ok_fd chk_c2 => /(_ erefl) E.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
    have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uincl_bool1 ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set P' := rcons P {| li_ii := ii; li_i := Lcond e lbl |}.
    have D' : disjoint_labels lbl1 lbl2 P'.
    + rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
      apply: disjoint_labels_wL _ D; lia.
    set Q' := {| li_ii := ii; li_i := Lgoto (fn, (lbl + 1)%positive) |} :: {| li_ii := ii; li_i := Llabel lbl |} :: lc1 ++ [:: {| li_ii := ii; li_i := Llabel (lbl + 1) |}].
    have C' : is_linear_of fn (P' ++ lc2 ++ Q' ++ Q).
    + by move: C; rewrite /P' /Q' /= -cats1 /= -!catA /= -!catA.
    have {E} [ m2 vm2 E K2 W2 X2 M2 ] := E m1 vm1 P' (Q' ++ Q) W1 M1 X1 D' C'.
    have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
    exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: M2 ].
    apply: lsem_step; last apply: lsem_trans.
    2: exact: E.
    + rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= ok_e' /= /setpc /=.
      by rewrite /P' /Q' /= size_rcons addn0.
    apply: LSem_step.
    rewrite catA in C'.
    rewrite /lsem1 /step -(addn0 (size (P' ++ lc2))) (find_instr_skip C') /= /eval_instr /li_i (eval_jumpE C') /= /setcpc /=.
    rewrite /P' -cats1.
    rewrite -!catA find_label_cat_hd; last by apply: D; lia.
    rewrite find_labelE /= find_label_cat_hd; last by apply: (valid_has_not_label V2); lia.
    rewrite find_labelE /= find_labelE /is_label /= next_lbl_neq find_label_cat_hd; last by apply: (valid_has_not_label V); lia.
    by rewrite find_labelE /is_label /= eqxx /= /setcpc /Q' !size_cat /= size_cat /= size_cat /= !addnS !addnA.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p extra_free_registers Pc Pi_r.
  Proof. Admitted.

  Local Lemma Hwhile_false : sem_Ind_while_false p extra_free_registers Pc Pi_r.
  Proof. Admitted.

  Lemma find_entry_label fn fd :
    sf_return_address (f_extra fd) ≠ RAnone →
    find_label xH (lfd_body (linear_fd p extra_free_registers fn fd)) = ok 0.
  Proof. by rewrite /linear_fd; case: sf_return_address. Qed.

  (* TODO: move next to the definition of match_mem *)
  (*Axiom mm_write_invalid : ∀ m m1' p s (w: word s),
    match_mem m m1' →
    (wunsigned (stack_limit m) <= wunsigned p ∧ wunsigned p + wsize_size s <= wunsigned (top_stack m))%Z →
    exists2 m2', write m1' p w = ok m2' & match_mem m m2'.*)

  Local Lemma Hcall : sem_Ind_call p extra_free_registers Pi_r Pfun.
  Proof.
    move => ii k s1 s2 ini res fn' args xargs xres ok_xargs ok_xres exec_call ih fn lbl /checked_iE[] fd ok_fd chk_call.
    case linear_eq: linear_i => [lbli li].
    move => fr_undef m1 vm2 P Q W M X D C.
    move: chk_call => /=.
    case: ifP => // fn'_neq_fn.
    case ok_fd': (get_fundef _ fn') => [ fd' | ] //; t_xrbindP => _ /assertP ok_ra _ /assertP ok_stk_sz _ /assertP ok_align _.
    have := get_fundef_p' ok_fd'.
    set lfd' := linear_fd _ _ _ fd'.
    move => ok_lfd'.
    move: linear_eq; rewrite /= ok_fd' fn'_neq_fn.
    move: (checked_prog ok_fd') => /=; t_xrbindP => - []; apply: add_finfoP => chk_body _ /assertP ok_to_save _ /assertP ok_save_stack _.
    have ok_body' : is_linear_of fn' (lfd_body lfd').
    - by rewrite /is_linear_of; eauto.
    move: ih; rewrite /Pfun; move => /(_ _ _ _ _ _ _ _ _ _ ok_body') ih A.
    have lbl_valid : (fn, lbl) \in (label_in_lprog p').
    - clear -A C ok_ra.
      apply: (label_in_lfundef _ C).
      case: sf_return_address A ok_ra => [ | ra | z ] //=.
      2: case: extra_free_registers => // ra.
      1-2: by case => _ <- _; rewrite /label_in_lcmd !pmap_cat /= !mem_cat inE eqxx !orbT.
    case ok_ptr: encode_label (encode_label_dom lbl_valid) => [ ptr | // ] _.
    case/sem_callE: (exec_call) => ? m s' k'; rewrite ok_fd' => /Some_inj <- ra_sem ok_ss sp_aligned T ok_m exec_cbody T' s2_eq.
    case ra_eq: (sf_return_address _) ok_ra ra_sem sp_aligned A => [ // | ra | z ] ok_ra ra_sem sp_aligned /=.
    { (* Internal function, return address in register [ra]. *)
      have ok_ra_of : is_ra_of fn' (RAreg ra) by rewrite /is_ra_of; exists fd'; assumption.
      move: ih => /(_ _ _ _ _ _ _ _ _ ok_ra_of) ih.
      case => ? ?; subst lbli li.
      case/andP: ra_sem => /andP[] ra_neq_GD ra_neq_RSP ra_not_written.
      move: C; rewrite /allocate_stack_frame; case: eqP => stack_size /= C.
      { (* Nothing to allocate *)
        set vm := vm2.[ra <- pof_val (vtype ra) (Vword ptr)]%vmap.
        have {W} W : wf_vm vm.
        + rewrite /vm => x; rewrite Fv.setP; case: eqP => ?; last exact: W.
          by subst; move/eqP: ok_ra => ->.
        move: C.
        set P' := P ++ _.
        move => C.
        have RA : value_of_ra m1 vm (RAreg ra) (Some ((fn, lbl), P', (size P).+2)).
        + rewrite /vm.
          case: (ra) ok_ra => /= ? vra /eqP ->; split.
          * exact: C.
          * rewrite /P' find_label_cat_hd; last by apply: D; rewrite /next_lbl; Psatz.lia.
            by rewrite /find_label /is_label /= eqxx /= addn2.
          exists ptr; first exact: ok_ptr.
          by rewrite Fv.setP_eq /= pword_of_wordE.
        move: ih => /(_ _ vm _ _ W M _ RA) ih.
        have XX : vm_uincl s1.[ra <- undef_error].[var_of_register RSP <- ok (pword_of_word (top_stack (emem s1)))]%vmap vm.
        + move => x; rewrite /vm Fv.setP; case: eqP.
          * move => ?; subst x.
            rewrite Fv.setP_neq //.
            move: (X (var_of_register RSP)).
            by rewrite T.
          move => _; move: x.
          apply: set_vm_uincl; first exact: X.
          by move/eqP: ok_ra => /= ->.
        have SP : is_sp_for_call fn' s1 (top_stack (emem s1)).
        + exists fd'; first exact: ok_fd'.
          move: sp_aligned.
          by rewrite /= ra_eq stack_size GRing.subr0.
        move: ih => /(_ _ XX SP).
        case => m' vm' exec_fn' K' W' X' M' ?; subst k.
        eexists; first apply: lsem_step; only 2: apply: lsem_step.
        + rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /= ok_ptr.
          rewrite /sem_sopn /= /write_var /= /to_estate /= /with_vm /= set_well_typed_var; last by apply/eqP.
          rewrite /= zero_extend_u wrepr_unsigned addn0.
          reflexivity.
        + rewrite /lsem1 /step -addn1 (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE ok_body').
          rewrite /lfd' find_entry_label; last by rewrite ra_eq.
          by rewrite /setcpc /=.
        + rewrite size_cat addn3; exact: exec_fn'.
        + rewrite -K' /vm => x x_notin_k.
          rewrite Fv.setP_neq //.
          apply/eqP; clear -x_notin_k.
          SvD.fsetdec.
        + exact: W'.
        + move => x; move: (X' x); rewrite Fv.setP; case: eqP; last by [].
          move => ?; subst => /=.
          case: vm'.[_]%vmap => //=.
          move => rsp /andP /= [] /cmp_le_antisym /(_ (pw_proof _)).
          case: rsp => /= ? rsp u ?; subst => /eqP.
          rewrite zero_extend_u => <- {rsp} /=.
          have := sem_one_varmap_facts.sem_call_valid_RSP exec_call.
          by rewrite /valid_RSP pword_of_wordE => ->.
        exact: M'.
      }
      (* Allocate a stack frame *)
      move: (X (var_of_register RSP)).
      rewrite T.
      case vm2_rsp: vm2.[_]%vmap => [ top_ptr | // ] /= /pword_of_word_uincl[].
      case: top_ptr vm2_rsp => ? ? le_refl vm2_rsp /= ? ?; subst.
      set top := (top_stack (emem s1) - wrepr U64 (stack_frame_allocation_size (f_extra fd')))%R.
      set vm  := vm2.[var_of_register RSP <- ok (pword_of_word top)].[ra <- pof_val (vtype ra) (Vword ptr)]%vmap.
      have {W} W : wf_vm vm.
      + rewrite /vm => x; rewrite Fv.setP; case: eqP => x_ra.
        * by subst; move/eqP: ok_ra => ->.
        rewrite Fv.setP; case: eqP => x_rsp; first by subst.
        exact: W.
      move: C.
      set P' := P ++ _.
      move => C.
      have RA : value_of_ra m1 vm (RAreg ra) (Some ((fn, lbl), P', size P + 3)).
      + rewrite /vm.
        case: (ra) ok_ra => /= ? vra /eqP ->; split.
        * exact: C.
        * rewrite /P' find_label_cat_hd; last by apply: D; rewrite /next_lbl; Psatz.lia.
           by rewrite /find_label /is_label /= eqxx /=.
         exists ptr; first exact: ok_ptr.
         by rewrite Fv.setP_eq /= pword_of_wordE.
      move: ih => /(_ _ vm _ _ W M _ RA) ih.
      have XX : vm_uincl s1.[ra <- undef_error].[var_of_register RSP <- ok (pword_of_word top)]%vmap vm.
      + move => x; rewrite /vm Fv.setP; case: eqP => x_rsp.
        * by subst; rewrite Fv.setP_neq // Fv.setP_eq.
        rewrite !(@Fv.setP _ _ ra); case: eqP => x_ra.
        * by subst; move/eqP: ok_ra => ->.
        rewrite Fv.setP_neq; last by apply/eqP.
        exact: X.
      have SP : is_sp_for_call fn' s1 top.
      + exists fd'; first exact: ok_fd'.
        by rewrite /= ra_eq.
      move: ih => /(_ _ XX SP).
      case => m' vm' exec_fn' K' W' X' M' ?; subst k.
      exists m' vm'.[var_of_register RSP <- ok (pword_of_word (top_stack (emem s1)))]%vmap.
      + apply: lsem_step; last apply: lsem_step; last apply: lsem_step; last apply: lsem_step_end.
        * rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /=.
          rewrite /sem_sopn /= /get_gvar /= /get_var vm2_rsp /= /sem_sop2 /=.
          rewrite /of_estate /with_vm /= !zero_extend_u addn0.
          reflexivity.
        * rewrite /lsem1 /step -addn1 (find_instr_skip C) /= /eval_instr /= ok_ptr.
          rewrite /sem_sopn /= /write_var /= /to_estate /= /with_vm /= set_well_typed_var; last by apply/eqP.
          rewrite /= zero_extend_u wrepr_unsigned addn1.
          reflexivity.
        * rewrite /lsem1 /step -addn2 (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE ok_body').
          rewrite /lfd' find_entry_label; last by rewrite ra_eq.
          by rewrite /setcpc /=.
        * rewrite pword_of_wordE; exact: exec_fn'.
        rewrite /lsem1 /step -addn1 -addnA (find_instr_skip C) /= /eval_instr /=.
        rewrite /sem_sopn /= /get_gvar /= /get_var.
        move: (X' (var_of_register RSP)).
        rewrite Fv.setP_eq /=.
        case: vm'.[_]%vmap => //= -[] ?? le_refl' /pword_of_word_uincl[] /= ??; subst.
        rewrite /= /of_estate /with_vm /= !zero_extend_u pword_of_wordE.
        rewrite size_cat /= -addn1 -addnA.
        rewrite -GRing.addrA GRing.addNr GRing.addr0.
        reflexivity.
      + move => x x_notin_k.
        rewrite Fv.setP; case: eqP => x_neq_rsp.
        * by subst; rewrite vm2_rsp pword_of_wordE.
        rewrite -K' // /vm !Fv.setP_neq //; apply/eqP => //.
        SvD.fsetdec.
      + move => x; rewrite Fv.setP; case: eqP => ?; last exact: W'.
        by subst.
      + have := sem_one_varmap_facts.sem_call_valid_RSP exec_call.
        rewrite /= /valid_RSP /set_RSP => h x /=.
        rewrite (Fv.setP vm'); case: eqP => x_rsp.
        * by subst; rewrite h.
        by move: (X' x); rewrite Fv.setP_neq //; apply/eqP.
      exact: M'.
    }
    (* Internal function, return address at offset [z]. *)
    case fr_eq: extra_free_registers ok_ra => [ fr | // ] /andP[] /andP[] /andP[] /andP[] fr_well_typed fr_neq_RSP z_pos z_bound sz_noof [] ? ?; subst lbli li.
    have ok_ra_of : is_ra_of fn' (RAstack z) by rewrite /is_ra_of; exists fd'; assumption.
    move: ih => /(_ _ _ _ _ _ _ _ _ ok_ra_of) ih.
    move: (X (var_of_register RSP)).
    rewrite T.
    case vm2_rsp: vm2.[_]%vmap => [ top_ptr | // ] /= /pword_of_word_uincl[].
    case: top_ptr vm2_rsp => ? ? le_refl vm2_rsp /= ? ?; subst.
    rewrite /allocate_stack_frame.
    case: ifP.
    + move => /eqP K; exfalso.
      case/andP: ok_stk_sz => /lezP A /lezP B.
      move/lezP: z_bound.
      move/lezP: z_pos.
      have := round_ws_range (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')).
      move: K A B; clear.
      rewrite /stack_frame_allocation_size.
      change (wsize_size Uptr) with 8%Z.
      lia.
    move => sz_nz k_eq.
    have : exists2 m1', write m1 (top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd'))
                  (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')) + wrepr U64 z)%R ptr = ok m1' &
                        match_mem s1 m1'.
    + apply: mm_write_invalid; first exact: M.
      have := (Memory.alloc_stackP ok_m).(ass_above_limit).
      rewrite (alloc_stack_top_stack ok_m).
      rewrite top_stack_after_aligned_alloc // wrepr_opp.
      move: ok_stk_sz z_pos z_bound sz_noof; clear.
      rewrite !zify -/(stack_frame_allocation_size (f_extra fd')) => - [] sz_pos extra_pos z_pos z_bound sz_noof.
      set L := stack_limit (emem s1).
      have L_range := wunsigned_range L.
      change (wsize_size Uptr) with 8%Z in *.
      move: (stack_frame_allocation_size _) z_bound sz_noof => S z_bound sz_noof.
      move: (top_stack (emem s1)) => T above_limit.
      have S_range : (0 <= S < wbase Uptr)%Z by lia.
      have X : (wunsigned (T - wrepr U64 S) <= wunsigned T)%Z.
      * move: (sf_stk_sz _) sz_pos above_limit => n; lia.
      have {X} TmS := wunsigned_sub_small S_range X.
      rewrite TmS in above_limit.
      have T_range := wunsigned_range T.
      rewrite wunsigned_add TmS; lia.
    case => m1' ok_m1' M1'.
    move: ih => /(_ _ _ _ _ _ M1') ih.
    move: fr_undef; rewrite fr_eq.
    move/eqP: fr_well_typed C fr_eq fr_neq_RSP.
    case: fr => ? fr /= -> C fr_eq fr_neq_RSP fr_undef.
    set vm1' := vm2.[var_of_register RSP <- ok (pword_of_word (top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd'))))].[ {| vtype := sword Uptr ; vname := fr |} <- ok (pword_of_word ptr)]%vmap.
    have {W} W : wf_vm vm1'.
    + rewrite /vm1' => x; rewrite Fv.setP; case: eqP => ?; first by subst.
      rewrite Fv.setP; case: eqP => ?; first by subst.
      exact: W.
    move: C.
    rewrite /allocate_stack_frame sz_nz /=.
    set body := P ++ _.
    move => C.
    set sp := top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')).
    have XX : vm_uincl s1.[var_of_register RSP <- ok (pword_of_word sp)] vm1'.
    + rewrite /vm1' => x; rewrite Fv.setP; case: eqP => x_rsp.
      * by subst; rewrite Fv.setP_neq // Fv.setP_eq.
      rewrite Fv.setP; case: eqP => x_fr.
      * by subst; rewrite fr_undef.
      by rewrite Fv.setP_neq // ; apply/eqP.
    move: ih => /(_ vm1' _ _ W XX).
    have RA : value_of_ra m1' vm1' (RAstack z) (Some ((fn, lbl), body, size P + 4)).
    + split.
      * exact: C.
      * rewrite /body find_label_cat_hd; last by apply: D; rewrite /next_lbl; lia.
        by do 5 rewrite find_labelE; rewrite /= /is_label /= eqxx.
      exists ptr; first by [].
      exists sp.
      * by rewrite /vm1' Fv.setP_neq // Fv.setP_eq.
      exact: writeP_eq ok_m1'.
    move => /(_ _ RA).
    have SP : is_sp_for_call fn' s1 sp.
    + exists fd'; first exact: ok_fd'.
      rewrite /= ra_eq; split; first by [].
      by rewrite /sp top_stack_after_aligned_alloc // wrepr_opp.
    move => /(_ SP) []m2' vm2' exec_fn' K' W' X' M'; subst k.
    exists m2' (vm2'.[var_of_register RSP <- ok (pword_of_word (sp + wrepr U64 (stack_frame_allocation_size (f_extra fd'))))])%vmap.
    - apply: lsem_step; only 2: apply: lsem_step; only 3: apply: lsem_step; only 4: apply: lsem_step; only 5: apply: lsem_trans.
      + rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /= /sem_sopn /= /get_gvar /= /get_var vm2_rsp /=.
        rewrite /of_estate pword_of_wordE !zero_extend_u -addn1 -addnA add0n.
        reflexivity.
      + rewrite /lsem1 /step (find_instr_skip C) /= /eval_instr /=.
        rewrite ok_ptr /sem_sopn /= /write_var /= /to_estate /= /with_vm /= wrepr_unsigned zero_extend_u.
        rewrite /= /of_estate /= addn1 -addn2.
        rewrite -wrepr_opp -top_stack_after_aligned_alloc; last by [].
        reflexivity.
      + rewrite /lsem1 /step (find_instr_skip C) /= /eval_instr /=.
        rewrite /sem_sopn /= /get_gvar /= /get_var Fv.setP_eq /=.
        rewrite /get_var Fv.setP_neq //.
        rewrite Fv.setP_eq /= !zero_extend_u pword_of_wordE.
        rewrite ok_m1' /with_mem /of_estate /=.
        rewrite -addn1 -addnA.
        reflexivity.
      + rewrite /lsem1 /step (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE ok_body').
        rewrite /lfd' find_entry_label; last by rewrite ra_eq.
        by rewrite /setcpc /=.
      + exact: exec_fn'.
      apply: LSem_step.
      rewrite -addn1 -addnA /lsem1 /step (find_instr_skip C) /= /eval_instr /=.
      rewrite /sem_sopn /= /get_gvar /= /get_var /=.
      move: (X' (var_of_register RSP)).
      rewrite Fv.setP_eq /=.
      case: vm2'.[_]%vmap => //= -[] ?? le_refl' /pword_of_word_uincl[] /= ??; subst.
      rewrite /= /of_estate /with_vm /= !zero_extend_u pword_of_wordE.
      by rewrite size_cat /= -addn1 -addnA.
    - move => x x_out.
      rewrite Fv.setP; case: eqP => x_rsp.
      + by subst; rewrite vm2_rsp pword_of_wordE /sp top_stack_after_aligned_alloc // wrepr_opp GRing.subrK.
      rewrite -K' // /vm1' !Fv.setP_neq //; apply/eqP => // ?; subst.
      apply: x_out.
      rewrite /extra_free_registers_at fr_eq; clear.
      SvD.fsetdec.
    - move => x; rewrite Fv.setP; case: eqP => ?; last exact: W'.
      by subst.
    - rewrite /sp top_stack_after_aligned_alloc // wrepr_opp GRing.subrK.
      move => x; rewrite Fv.setP; case: eqP => x_rsp.
      + subst.
        by rewrite (sem_call_stack_stable exec_call).(ss_top_stack) s2_eq /= /set_RSP Fv.setP_eq.
      by move: (X' x); rewrite Fv.setP_neq //; apply/eqP.
    exact: M'.
  Qed.

  Lemma vm_uincl_set_RSP m vm vm' :
    vm_uincl vm vm' →
    vm_uincl (set_RSP m vm) (set_RSP m vm').
  Proof. move => h; apply: (set_vm_uincl h); exact: pval_uincl_refl. Qed.

  Local Lemma Hproc : sem_Ind_proc p extra_free_registers Pc Pfun.
  Proof.
    red => ii k s1 _ fn fd m1' s2' ok_fd free_ra ok_ss rsp_aligned valid_rsp ok_m1' exec_body ih valid_rsp' -> m1 vm1 _ ra lret sp W M X [] fd' ok_fd' <- [].
    rewrite ok_fd => _ /Some_inj <- ?; subst ra.
    rewrite /value_of_ra => ok_lret.
    case; rewrite ok_fd => _ /Some_inj <- /= ok_sp.
    move: (checked_prog ok_fd) => /=; t_xrbindP => - []; apply: add_finfoP => chk_body _ /assertP ok_to_save _ /assertP ok_save_stack _.
    have ? : fd' = linear_fd p extra_free_registers fn fd.
    - move: linear_ok ok_fd ok_fd'; clear.
      rewrite /linear_prog; t_xrbindP => _ _ _ _ <- /=.
      by rewrite /get_fundef assoc_map2 => -> [].
    subst fd'.
    move: ok_fd'; rewrite /linear_fd.
    case: sf_return_address free_ra ok_to_save ok_save_stack X ok_lret exec_body ih ok_sp =>
      /= [ _ ok_to_save ok_save_stack | ra free_ra _ _ | rastack free_ra _ _ ] X ok_lret exec_body ih.
    2-3: case => sp_aligned.
    all: move => ?; subst sp.
    - (* Export function *)
    { case: lret ok_lret => // _.
      case: sf_save_stack ok_save_stack ok_ss exec_body ih =>
      [ | saved_rsp | stack_saved_rsp ] /= ok_save_stack ok_ss exec_body ih ok_fd'.
      + (* No need to save RSP *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        case: (linear_c fn) ok_fd' => lbl lbody /= ok_fd' E.
        have ok_body : is_linear_of fn (lbody ++ [::]).
        + by rewrite /is_linear_of cats0 ok_fd' /=; eauto.
        have M' := mm_alloc M ok_m1'.
        case/andP: ok_save_stack => /andP[] /eqP sf_align_1 /eqP stk_sz_0 /eqP stk_extra_sz_0.
        have top_stack_preserved : top_stack m1' = top_stack (s1: mem).
        + rewrite (alloc_stack_top_stack ok_m1') sf_align_1.
          rewrite Memory.top_stack_after_aligned_alloc.
          2: exact: is_align8.
          by rewrite stk_sz_0 stk_extra_sz_0 -addE add_0.
        have X' : vm_uincl (set_RSP m1' (kill_flags s1 rflags)) vm1.
        + rewrite /set_RSP top_stack_preserved.
          apply: vm_uincl_trans X.
          apply: set_vm_uincl; last exact: eval_uincl_refl.
          exact: kill_flags_uincl.
        have {E} [m2 vm2] := E m1 vm1 [::] [::] W M' X' (λ _ _, erefl) ok_body.
        rewrite /= => E K2 W2 X2 M2.
        eexists m2 _; [ exact: E | | exact: W2 | | exact: mm_free M2 ].
        + apply: vmap_eq_exceptI; last exact: K2.
          SvD.fsetdec.
        have S : stack_stable m1' s2'.
        + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
        move => x; move: (X2 x); rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
        by rewrite valid_rsp' -(ss_top_stack S) top_stack_preserved.
      }
      + (* RSP is saved into register “saved_rsp” *)
      { admit. }
      (* RSP is saved in stack at offset “stack_saved_rsp” *)
      { admit. }
    }
    - (* Internal function, return address in register “ra” *)
    { case: ra X free_ra ok_lret exec_body ih => // -[] // [] // ra X /andP[] _ ra_notin_k.
      case: lret => // - [] [] [] caller lret cbody pc [] ok_cbody ok_pc [] retptr ok_retptr ok_ra exec_body ih.
      have {ih} := ih fn 2%positive.
      rewrite /checked_c ok_fd chk_body => /(_ erefl).
      rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
      case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have X1 : vm_uincl (set_RSP m1' (s1.[{| vtype := sword64; vname := ra |} <- undef_error])) vm1.
      + move => x; move: (X x).
        rewrite /set_RSP (alloc_stack_top_stack ok_m1').
        rewrite top_stack_after_aligned_alloc;
          last by exact: sp_aligned.
        rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
        exact.
      have D : disjoint_labels 2 lbl [:: P].
      + by move => q [A B]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      have {E} [ m2 vm2 E K2 W2 ok_vm2 M2 ] := E m1 vm1 [:: P] Q W (mm_alloc M ok_m1') X1 D ok_body.
      eexists; [ | | exact: W2 | | exact: mm_free M2 ].
      + apply: lsem_trans; first exact: E.
        apply: LSem_step.
        rewrite catA in ok_body.
        rewrite /lsem1 /step -(addn0 (size ([:: P] ++ lbody))) (find_instr_skip ok_body) /= /eval_instr /= /get_gvar /= /get_var /=.
        have ra_not_written : (vm2.[ Var sword64 ra ] = vm1.[ Var sword64 ra ])%vmap.
        * symmetry; apply: K2.
          by apply/Sv_memP.
        rewrite ra_not_written ok_ra /= zero_extend_u.
        have := decode_encode_label (label_in_lprog p') (caller, lret).
        rewrite ok_retptr /= => -> /=.
        case: ok_cbody => fd' -> -> /=; rewrite ok_pc /setcpc /=; reflexivity.
      + apply: vmap_eq_exceptI K2.
        SvD.fsetdec.
      move => ?; rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
      move: (ok_vm2 (var_of_register RSP)).
      have S : stack_stable m1' s2'.
      + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
      rewrite valid_rsp' -(ss_top_stack S) (alloc_stack_top_stack ok_m1').
      rewrite top_stack_after_aligned_alloc;
        last by exact: sp_aligned.
      by rewrite wrepr_opp.
    }
    (* Internal function, return address in stack at offset “rastack” *)
    { admit. }
  Admitted.

  Lemma linear_fdP ii k s1 fn s2 :
    sem_call p extra_free_registers ii k s1 fn s2 →
    Pfun ii k s1 fn s2.
  Proof.
    exact: (@sem_call_Ind p extra_free_registers Pc Pi Pi_r Pfun Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hcall Hproc).
  Qed.

  (*
  Lemma linear_fdP:
    forall fn m1 va m2 vr,
    sem_call p wrip m1 fn va m2 vr -> lsem_fd p' wrip m1 fn va m2 vr.
  Proof.
    move=> fn m1 va m2 vr [] {fn m1 va m2 vr}.
    move=> m1 m2 fn sf vargs vargs' s0 s1 s2 vres vres' Hsf Hargs Hi Hw Hbody Hres Htyo Hfi.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => _ /assertP _ funcs H0' hp'. 
    rewrite -hp'. 
    have [f' Hf'1 Hf'2] := (get_map_cfprog H0' Hsf).
    have Hf'3 := Hf'1.
    apply: rbindP Hf'3=> [l Hc] [] Hf'3.
    rewrite /add_finfo in Hc.
    case Heq: linear_c Hc=> [[lblc lc]|] //= [] Hl.
    rewrite linear_c_nil in Heq.
    apply: rbindP Heq=> [[lblc' lc']] Heq [] Hz1 Hz2.
    have [_ _ H] := linear_cP Heq.
    move: Hbody=> /H /(@lsem_cat_tl [::]) Hs.
    rewrite -Hf'3 in Hf'2.
    move: Hi; rewrite /init_state /= /init_stk_state; t_xrbindP => /= m1' Halloc [].
    rewrite /with_vm /= => ?;subst s0.
    move: Hfi; rewrite /finalize /= /finalize_stk_mem => ?; subst m2.
    apply: LSem_fd; eauto => //=.
    rewrite -Hl /=.
    move: Hs; rewrite /= Hz2 !setc_of_estate.
    have -> // : size lc' = size lc.
    by rewrite -Hz2 size_cat addn0.
  Qed.
   *)

End PROOF.

(* left overs 
  Lemma of_estate_add_hd_c s fn li lc pc:
    add_hd_c li (of_estate s fn lc pc) = of_estate s fn (li ++ lc) (size li + pc).
  Proof. done. Qed.

  Lemma to_of_estate s fn c pc : to_estate (of_estate s fn c pc) = s.
  Proof. by case: s. Qed.

  Lemma find_label_hd lbl ii c :
    find_label lbl ({|li_ii:= ii; li_i := Llabel lbl|} :: c ) = ok 0.
  Proof. by rewrite /find_label /= /is_label /= eqxx. Qed.

  Lemma setc_of_estate s c pc c' :setc (of_estate s c pc) c' = of_estate s c' pc.
  Proof. done. Qed.

  Lemma lc_of_estate s lc pc : linear_sem.lc (of_estate s lc pc) = lc.
  Proof. by case: s. Qed.

  Lemma setpc_of_estate s C pc pc' : setpc (of_estate s C pc) pc' = of_estate s C pc'.
  Proof. done. Qed.
*)
