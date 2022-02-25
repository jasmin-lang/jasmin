(* ** Imports and settings *)

Require memory_example.

Import all_ssreflect all_algebra.
Import ZArith.
Import type word utils.
Import memory_example.
Export memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Memory := MemoryI.

Notation mem := Memory.mem.

Definition eq_mem m m' : Prop :=
    forall ptr sz, read_mem m ptr sz = read_mem m' ptr sz.

Lemma eq_mem_refl m : eq_mem m m.
Proof. by []. Qed.

Lemma eq_mem_sym m m' : eq_mem m m' -> eq_mem m' m.
Proof. move => h ptr sz; symmetry; exact: (h ptr sz). Qed.

Lemma eq_mem_trans m2 m1 m3 :
  eq_mem m1 m2 ->
  eq_mem m2 m3 ->
  eq_mem m1 m3.
Proof. move => p q x y; rewrite (p x y); exact: (q x y). Qed.

Lemma read_mem_valid_pointer m ptr sz w :
  read_mem m ptr sz = ok w ->
  valid_pointer m ptr sz.
Proof.
  by move => hr; apply /Memory.readV;exists w.
Qed.

Lemma write_mem_valid_pointer m ptr sz w m' :
  write_mem m ptr sz w = ok m' ->
  valid_pointer m ptr sz.
Proof.
  move => hw; apply /Memory.writeV; exists m'; exact hw.
Qed.

Lemma write_mem_can_read m ptr sz w m' :
  write_mem m ptr sz w = ok m' ->
  exists w', read_mem m ptr sz = ok w'.
Proof. by move => /write_mem_valid_pointer /Memory.readV. Qed.
