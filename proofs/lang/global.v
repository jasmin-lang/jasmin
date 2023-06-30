(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export xseq ZArith strings word utils ident type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ---------------------------------------------------------------------- *)

Record global := Global { size_of_global : wsize ; ident_of_global:> Ident.ident }.

Definition global_beq (g1 g2: global) : bool :=
  let 'Global s1 n1 := g1 in
  let 'Global s2 n2 := g2 in
  (s1 == s2) && (n1 == n2).

Lemma global_eq_axiom : Equality.axiom global_beq.
Proof.
  case => s1 g1 [] s2 g2 /=; case: andP => h; constructor.
  - by case: h => /eqP -> /eqP ->.
  by case => ??; apply: h; subst.
Qed.

Definition global_eqMixin := Equality.Mixin global_eq_axiom.
Canonical global_eqType := Eval hnf in EqType global global_eqMixin.

(* ---------------------------------------------------------------------- *)

Definition glob_decl := (global * Z)%type.
Notation glob_decls  := (seq glob_decl).

(* ---------------------------------------------------------------------- *)
Definition get_global_Z (gd: glob_decls) (g: global) : option Z :=
  assoc gd g.

Definition get_global_word gd g : exec (word (size_of_global g)) :=
  if get_global_Z gd g is Some z then
    ok (wrepr (size_of_global g) z)
  else type_error.

