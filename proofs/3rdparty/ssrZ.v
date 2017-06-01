(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import ZArith.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.
Local Open Scope ring_scope.

Import GRing.Theory.

(* -------------------------------------------------------------------- *)
Lemma ZeqbP (x y : Z) : reflect (x = y) (x =? y)%Z.
Proof. by apply: (iffP idP) => /Z.eqb_eq. Qed.

Definition Z_eqMixin := EqMixin ZeqbP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

(* -------------------------------------------------------------------- *)
Module ZCode.
Definition encode (z : Z) :=
  match z with
  | 0%Z     => GenTree.Node 0 [::]
  | Z.pos p => GenTree.Node 1 [:: GenTree.Leaf (Pos.to_nat p)]
  | Z.neg p => GenTree.Node 2 [:: GenTree.Leaf (Pos.to_nat p)]
  end.

Definition decode t :=
  match t with
  | GenTree.Node 0 [::] =>
      Some 0%Z
  | GenTree.Node 1 [:: GenTree.Leaf n] =>
      Some (Z.pos (Pos.of_nat n))
  | GenTree.Node 2 [:: GenTree.Leaf n] =>
      Some (Z.neg (Pos.of_nat n))
  | _ => None
  end.

Lemma encodeK : pcancel encode decode.
Proof. by case => //= p; rewrite Pos2Nat.id. Qed.
End ZCode.

Definition Z_choiceMixin := PcanChoiceMixin ZCode.encodeK.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.

Definition Z_countMixin := PcanCountMixin ZCode.encodeK.
Canonical Z_countType := Eval hnf in CountType Z Z_countMixin.

(* -------------------------------------------------------------------- *)
Definition Z_zmodMixin :=
  ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
Canonical Z_zmodType := Eval hnf in ZmodType Z Z_zmodMixin.

(* -------------------------------------------------------------------- *)
Definition Z_ringMixin := ComRingMixin
  Z.mul_assoc Z.mul_comm Z.mul_1_l Z.mul_add_distr_r (erefl _).
Canonical Z_ringType := Eval hnf in RingType Z Z_ringMixin.
Canonical Z_comRingType := Eval hnf in ComRingType Z Z.mul_comm.

(* -------------------------------------------------------------------- *)
Definition unitZ := [qualify a z : Z | (z == 1) || (z == -1)].
Definition invZ z : Z := z.

Module ZUnitRing.
Lemma mulVZ : {in unitZ, left_inverse 1%R invZ *%R}.
Proof. by move=> z /pred2P[] ->. Qed.

Lemma unitZPl m n : n * m = 1 -> m \is a unitZ.
Proof. by rewrite mulrC=> /Z.eq_mul_1 [] ->. Qed.

Lemma  invZ_out : {in [predC unitZ], invZ =1 id}.
Proof. exact. Qed.

Lemma idomain_axiomZ (m n : Z) : m * n = 0 -> (m == 0) || (n == 0).
Proof. by move/Z.eq_mul_0; case=> ->; rewrite ?orbT. Qed.

Definition comMixin := ComUnitRingMixin mulVZ unitZPl invZ_out.
End ZUnitRing.

Canonical Z_unitRingType :=
  Eval hnf in UnitRingType Z ZUnitRing.comMixin.
Canonical int_comUnitRing :=
  Eval hnf in [comUnitRingType of Z].
Canonical int_iDomain :=
  Eval hnf in IdomainType Z ZUnitRing.idomain_axiomZ.

(* -------------------------------------------------------------------- *)
Lemma ZleP {x y} : reflect (x <= y)%Z (x <=? y)%Z.
Proof. by apply: (iffP idP) => /Z.leb_le. Qed.

(* -------------------------------------------------------------------- *)
Lemma ZltP {x y} : reflect (x < y)%Z (x <? y)%Z.
Proof. by apply: (iffP idP) => /Z.ltb_lt. Qed.

(* -------------------------------------------------------------------- *)
Module ZOrdered.
Lemma leZ_norm_add x y : Z.abs (x + y) <=? Z.abs x + Z.abs y.
Proof. by rewrite -(rwP ZleP); apply: Z.abs_triangle. Qed.

Lemma ltZ_add x y : 0 <? x -> 0 <? y -> 0 <? x + y.
Proof. by move=> gt0_x gt0_y; apply/ZltP/Z.add_pos_pos; apply/ZltP. Qed.

Lemma eq0_normZ x : Z.abs x = 0 -> x = 0.
Proof. by move/Z.abs_0_iff. Qed.

Lemma leZ_total x y : (x <=? y) || (y <=? x).
Proof. by apply/orP; rewrite -!(rwP ZleP); apply: Z.le_ge_cases. Qed.

Lemma normZM : {morph (fun n => Z.abs n) : x y / x * y}.
Proof. by move=> x y; rewrite Z.abs_mul. Qed.

Lemma subZ_ge0 m n : (0 <=? (n - m)) = (m <=? n).
Proof. by apply/ZleP/ZleP => /Z.le_0_sub. Qed.

Lemma leZ_def x y : (x <=? y) = (Z.abs (y - x) == y - x).
Proof. by rewrite -subZ_ge0; apply/ZleP/eqP => /Z.abs_eq_iff. Qed.

Lemma ltZ_def x y : (x <? y) = (y != x) && (x <=? y).
Proof.
apply/ZltP/andP=> [|[/eqP ne_xy /ZleP]]; last first.
+ by case/Zle_lt_or_eq => // /esym.
move=> lt_xy; rewrite eq_sym; split; first by apply/eqP/Z.lt_neq.
apply/ZleP/(Z.le_trans _ (Z.succ x))/Zlt_le_succ => //.
by apply/Z.le_succ_diag_r.
Qed.

Definition Mixin := NumMixin
  leZ_norm_add ltZ_add eq0_normZ (in2W leZ_total) normZM leZ_def ltZ_def.
End ZOrdered.

Canonical Z_numDomainType := NumDomainType Z ZOrdered.Mixin.
Canonical Z_realDomainType := RealDomainType Z (ZOrdered.leZ_total 0).
