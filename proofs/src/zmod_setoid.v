Require Import Setoid Morphisms ZArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq choice eqtype.
Open Scope Z_scope.

Section EqMod.

Variable n : Z.

Definition eqmod (x y:Z) := (x mod n) = (y mod n).

Instance relation_eqmod : Equivalence eqmod.
Proof.
  constructor=> //.
  by move=> x y z;rewrite /eqmod => -> ->.
Qed.

Instance Zadd_eqmod : Proper (eqmod ==> eqmod ==> eqmod) Z.add.
Proof.
  rewrite /eqmod=> x1 x2 Heq1 y1 y2 Heq2.
  by rewrite Zplus_mod Heq1 Heq2 -Zplus_mod.
Qed.

Instance Zminus_eqmod : Proper (eqmod ==> eqmod ==> eqmod) Z.sub.
Proof.
  rewrite /eqmod=> x1 x2 Heq1 y1 y2 Heq2.
  by rewrite Zminus_mod Heq1 Heq2 -Zminus_mod.
Qed.

Instance Zmul_eqmod : Proper (eqmod ==> eqmod ==> eqmod) Z.mul.
Proof.
  rewrite /eqmod=> x1 x2 Heq1 y1 y2 Heq2.
  by rewrite Zmult_mod Heq1 Heq2 -Zmult_mod.
Qed.

Lemma mod_is_0 : eqmod n 0.
Proof. by rewrite /eqmod Z_mod_same_full Zmod_0_l. Qed.

End EqMod.

Module Test.

(* FIXME: Can we make EqMod a functor and get these instances automatically *)
Definition p64 := 2^64.
Definition eqmod64 (x y : Z) := x mod p64 = y mod p64.
Instance relation_eqmod64 : Equivalence eqmod64 := relation_eqmod p64.
Instance Zadd_eqmod64   : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.add := Zadd_eqmod p64.
Instance Zminus_eqmod64 : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.sub := Zminus_eqmod p64.
Instance Zmul_eqmod64   : Proper (eqmod64 ==> eqmod64 ==> eqmod64) Z.mul := Zmul_eqmod p64.
Lemma p64_is_0 : eqmod64 p64 0. Proof. by rewrite (mod_is_0 p64). Qed.

Lemma test (x y z:Z) :
  (x*p64 + y*p64*p64 + z - z*p64) mod p64 = z mod p64.
Proof.
  rewrite -/(eqmod64  _ _) p64_is_0 /eqmod64. f_equal. ring.
Qed.

End Test.