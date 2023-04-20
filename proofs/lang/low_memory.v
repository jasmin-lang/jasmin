(* ** Imports and settings *)

From Coq Require Import RelationClasses.
Require memory_example.

Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import Lia.
Import Utf8 ZArith.
Import ssrring.
Import type word utils.
Import memory_example.
Export memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Memory := MemoryI.

Notation mem := Memory.mem.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

(* -------------------------------------------------------------- *)
Definition eq_mem m m' : Prop :=
  forall ptr sz, read m ptr sz = read m' ptr sz.

Lemma eq_mem_refl m : eq_mem m m.
Proof. by []. Qed.

Lemma eq_mem_sym m m' : eq_mem m m' -> eq_mem m' m.
Proof. move => h ptr sz; symmetry; exact: (h ptr sz). Qed.

Lemma eq_mem_trans m2 m1 m3 :
  eq_mem m1 m2 ->
  eq_mem m2 m3 ->
  eq_mem m1 m3.
Proof. move => p q x y; rewrite (p x y); exact: (q x y). Qed.

(* -------------------------------------------------------------- *)
#[ global ]
Instance stack_stable_equiv : Equivalence stack_stable.
Proof.
  split.
  - by [].
  - by move => x y [*]; split.
  move => x y z [???] [???]; split; etransitivity; eassumption.
Qed.

Lemma ss_top_stack a b :
  stack_stable a b →
  top_stack a = top_stack b.
Proof. by rewrite /top_stack => s; rewrite (ss_frames s) (ss_root s). Qed.

(* -------------------------------------------------------------- *)
Lemma write_validw m ptr sz (w:word sz) m' :
  write m ptr w = ok m' ->
  validw m ptr sz.
Proof.
  move => hw; apply /writeV; exists m'; exact hw.
Qed.

(* An alternate form of [CoreMem.writeP_neq] that should be easier to use. *)
Lemma writeP_neq mem1 mem2 p ws (v : word ws) p2 ws2 :
  write mem1 p v = ok mem2 ->
  disjoint_range p ws p2 ws2 ->
  read mem2 p2 ws2 = read mem1 p2 ws2.
Proof.
  move=> hmem2 hdisj.
  apply (writeP_neq hmem2).
  by apply disjoint_range_alt.
Qed.

Lemma disjoint_range_valid_not_valid_U8 m p1 ws1 p2 :
  validw m p1 ws1 ->
  ~ validw m p2 U8 ->
  disjoint_range p1 ws1 p2 U8.
Proof.
  move=> /validwP [hal1 hval1] hnval.
  split.
  + by apply is_align_no_overflow.
  + by apply is_align_no_overflow; apply is_align8.
  rewrite wsize8.
  case: (Z_le_gt_dec (wunsigned p1 + wsize_size ws1) (wunsigned p2)); first by left.
  case: (Z_le_gt_dec (wunsigned p2 + 1) (wunsigned p1)); first by right.
  move=> hgt1 hgt2.
  case: hnval.
  apply /validwP; split.
  + by apply is_align8.
  move=> k; rewrite wsize8 => hk; have ->: k = 0%Z by Lia.lia.
  rewrite add_0.
  have ->: p2 = (p1 + wrepr _ (wunsigned p2 - wunsigned p1))%R.
  + by rewrite wrepr_sub !wrepr_unsigned; ssring.
  by apply hval1; Lia.lia.
Qed.

Lemma alloc_stack_top_stack m ws sz ioff sz' m' :
  alloc_stack m ws sz ioff sz' = ok m' →
  top_stack m' = top_stack_after_alloc (top_stack m) ws (sz + sz').
Proof.
  rewrite /top_stack => /Memory.alloc_stackP a.
  by rewrite a.(ass_frames).
Qed.

(* -------------------------------------------------------------- *)
Lemma wunsigned_sub_small (p: pointer) (n: Z) :
  (0 <= n < wbase Uptr →
  wunsigned (p - wrepr Uptr n ) <= wunsigned p →
  n <= wunsigned p)%Z.
Proof.
  move => n_range.
  rewrite wunsigned_sub_if; case: word_ssrZ.leZP; rewrite wunsigned_repr_small //.
  Lia.lia.
Qed.

Lemma aligned_alloc_no_overflow m ws sz ioff sz' m' :
  (0 <= sz →
  0 <= sz' →
  round_ws ws (sz + sz') < wbase Uptr →
  is_align (top_stack m) ws →
  alloc_stack m ws sz ioff sz' = ok m' →
  round_ws ws (sz + sz') <= wunsigned (top_stack m))%Z.
Proof.
  move => sz_pos sz'_pos no_ovf AL A; apply: wunsigned_sub_small.
  - have [L _] := round_ws_range ws (sz + sz').
    Lia.lia.
  etransitivity; last exact: (proj2 (Memory.alloc_stackP A).(ass_above_limit)).
  rewrite (alloc_stack_top_stack A) (top_stack_after_aligned_alloc _ AL) wrepr_opp.
  Lia.lia.
Qed.

(* -------------------------------------------------------------- *)
Definition allocatable_stack (m : mem) (z : Z) :=
  (0 <= z <= wunsigned (top_stack m) - wunsigned (stack_limit m))%Z.

(* -------------------------------------------------------------- *)
Local Open Scope Z_scope.

Definition fill_mem (m : mem) (p : pointer) (l : list u8) : exec mem := 
  Let pm :=
   foldM (fun w pm =>
             Let m := write pm.2 (add p pm.1) w in 
             ok (pm.1 + 1, m)) (0%Z, m) l in
    ok pm.2.

Lemma fill_mem_stack_stable m1 m2 ptr bytes :
  fill_mem m1 ptr bytes = ok m2 ->
  stack_stable m1 m2.
Proof.
  rewrite /fill_mem; t_xrbindP=> -[z2 {m2}m2] /= hfold <-.
  elim: bytes 0 m1 hfold => [ | b bytes ih] z1 m1 /=.
  + by move=> [_ <-].
  t_xrbindP=> _ m1' hw <- /ih{ih}ih.
  by rewrite (Memory.write_mem_stable hw).
Qed.

Lemma fill_mem_validw_eq m1 m2 ptr bytes :
  fill_mem m1 ptr bytes = ok m2 ->
  validw m1 =2 validw m2.
Proof.
  rewrite /fill_mem; t_xrbindP=> -[z2 {m2}m2] /= hfold <-.
  elim: bytes 0 m1 hfold => [ | b bytes ih] z1 m1 /=.
  + by move=> [_ <-].
  t_xrbindP=> _ m1' hw <- /ih{ih}ih.
  move=> p ws.
  by rewrite -(write_validw_eq hw) ih.
Qed.

Lemma fill_mem_read8 m1 m2 ptr bytes :
  Z.of_nat (size bytes) <= wbase Uptr ->
  fill_mem m1 ptr bytes = ok m2 ->
  forall k, read m2 k U8 = 
    let i := sub k ptr in
    if (0 <=? i) && (i <? Z.of_nat (size bytes))
    then ok (nth 0%R bytes (Z.to_nat i))
    else read m1 k U8.
Proof.
  move=> hover.
  rewrite /fill_mem; t_xrbindP=> -[z2 {m2}m2] /= hfold <- k.
  have: forall z1,
    0 <= z1 /\ z1 + Z.of_nat (size (bytes)) <= wbase Uptr ->
    foldM (fun w pm => Let m := write pm.2 (add ptr pm.1) w in ok (pm.1 + 1, m)) (z1, m1) bytes = ok (z2, m2) ->
    read m2 k U8 =
      let i := sub k ptr - z1 in
      if (0 <=? i) && (i <? Z.of_nat (size bytes))
      then ok (bytes`_(Z.to_nat i))%R
      else read m1 k U8;
    last first.
  + have ? := wunsigned_range ptr.
    move=> /(_ 0 ltac:(lia) hfold).
    by rewrite Z.sub_0_r.
  elim: bytes m1 {hfold hover} => [ | b bytes ih] m1 z1 /=.
  + move=> _ [_ <-].
    by case: ifP => //; rewrite !zify; lia.
  t_xrbindP=> hz1 _ m1' hw <- /ih -> /=; last by lia.
  have ->:
    (0 <=? sub k ptr - z1) && (sub k ptr - z1 <? Pos.of_succ_nat (size bytes)) =
    (sub k ptr == z1) || (0 <=? sub k ptr - (z1 + 1)) && (sub k ptr - (z1 + 1) <? Z.of_nat (size bytes)).
  + by apply /idP/idP; rewrite !zify (rwR2 (@eqP _)); lia.
  move: hw; rewrite -set_write8 => hw.
  rewrite -!get_read8 (setP _ hw) orbC.
  case: ifP => /=.
  + rewrite !zify => h.
    by have ->: Z.to_nat (sub k ptr - z1) = S (Z.to_nat (sub k ptr - (z1+1))) by lia. 
  move=> _.
  case: eqP => [<- | hne].
  + have ->: sub (add ptr z1) ptr = z1.
    + rewrite subE addE (GRing.addrC ptr) GRing.addrK.
      by apply wunsigned_repr_small; lia.
    by rewrite eq_refl Z.sub_diag.
  by case: eqP => // heq; case: hne; rewrite -heq add_sub.
Qed.

Lemma fill_mem_read8_no_overflow (m1 m2:mem) (ptr:pointer) (bytes:seq u8) :
  Z.of_nat (size bytes) <= wbase Uptr ->
  fill_mem m1 ptr bytes = ok m2 ->
  forall k, 0 <= k < wbase Uptr ->
    read m2 (ptr + wrepr Uptr k)%R U8 =
      if (0 <=? k) && (k <? Z.of_nat (size bytes))
      then ok (nth 0%R bytes (Z.to_nat k))
      else read m1 (ptr + wrepr Uptr k)%R U8.
Proof.
  move=> hover hfillm k hk.
  have -> := fill_mem_read8 hover hfillm.
  have -> //: sub (ptr + wrepr Uptr k)%R ptr = k.
  rewrite subE (GRing.addrC ptr) GRing.addrK.
  by apply wunsigned_repr_small.
Qed.

Lemma fill_mem_disjoint m1 m2 ptr bytes :
  fill_mem m1 ptr bytes = ok m2 ->
  forall p ws,
  disjoint_zrange ptr (Z.of_nat (size bytes)) p (wsize_size ws) ->
  read m2 p ws = read m1 p ws.
Proof.
  move=> hfillm p ws [].
  rewrite /no_overflow !zify => hover1 hover2 hdisj.
  have hrange1 := wunsigned_range ptr.
  have hrange2 := wunsigned_range p.
  apply eq_read => i hi.
  rewrite (fill_mem_read8 _ hfillm) /=; last by lia.
  set b := (X in if X then _ else _).
  have -> //: b = false.
  rewrite /b subE addE.
  apply /negP; rewrite !zify.
  rewrite wunsigned_sub_if wunsigned_add; last by lia.
  case: ifP; lia.
Qed.

End WITH_POINTER_DATA.
