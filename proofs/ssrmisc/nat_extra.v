From mathcomp Require Import all_ssreflect.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section NatOrder.

  Inductive nat_ge m : nat -> Prop :=
  | ge_n : nat_ge m 0
  | ge_S n of (n < m) : nat_ge m n -> nat_ge m n.+1.

  Lemma nat_geP m n : reflect (nat_ge m n) (n <= m).
  Proof.
    apply: (iffP idP); last by elim: n /.
    elim: n => [_|n IHn ltnm]; first by apply/ge_n.
    by apply/ge_S => //; apply/IHn/ltnW.
  Qed.

  Lemma nat_le_ind_eq (P : nat -> Prop) m :
    P 0 ->
    (forall n, n < m -> P n -> P n.+1) ->
    P m.
  Proof.
    move => HP0 IHP; have: nat_ge m m by apply/nat_geP.
    by apply/(@nat_ge_ind m P) => // n ltnm _; apply/IHP.
  Qed.

End NatOrder.
