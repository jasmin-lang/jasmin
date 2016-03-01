(* -------------------------------------------------------------------- *)
Require Import ssreflect eqtype ssrbool choice ssrfun seq.
Require Export String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition ascii_eq (a1 a2 : Ascii.ascii) :=
  nosimpl (compareb Ascii.ascii_dec a1 a2).

Lemma ascii_eqP (a1 a2 : Ascii.ascii) :
  reflect (a1 = a2) (ascii_eq a1 a2).
Proof. by apply/compareP. Qed.

Definition ascii_eqMixin := EqMixin ascii_eqP.
Canonical  ascii_eqType  := EqType Ascii.ascii ascii_eqMixin.

Definition ascii_choiceMixin := CanChoiceMixin Ascii.ascii_nat_embedding.
Canonical  ascii_choiceType  := ChoiceType Ascii.ascii ascii_choiceMixin.

Definition ascii_countMixin := CanCountMixin Ascii.ascii_nat_embedding.
Canonical  ascii_countType  := CountType Ascii.ascii ascii_countMixin.

(* -------------------------------------------------------------------- *)
Definition string_eq (s1 s2 : string) :=
  nosimpl (compareb string_dec s1 s2).

Lemma string_eqP (s1 s2 : string) :
  reflect (s1 = s2) (string_eq s1 s2).
Proof. by apply/compareP. Qed.

Definition string_eqMixin := EqMixin string_eqP.
Canonical  string_eqType  := EqType string string_eqMixin.

Fixpoint code (s : string) :=
  if s is String a s then a :: code s else [::].

Fixpoint decode (s : seq Ascii.ascii) :=
  if s is a :: s then String a (decode s) else EmptyString.

Lemma codeK : cancel code decode.
Proof. by elim=> //= a s ->. Qed.

Definition string_choiceMixin := CanChoiceMixin codeK.
Canonical  string_choiceType  := ChoiceType string string_choiceMixin.

Definition string_countMixin := CanCountMixin codeK.
Canonical  string_countType  := CountType string string_countMixin.
