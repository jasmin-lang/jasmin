From mathcomp Require Import all_ssreflect.
Require Import Utf8 oseq xseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section AssocOnth.

  Lemma assoc_onth (T : eqType) (U : Type) (s : seq (T * U)) (x : T) (y : U) :
    assoc s x = Some y ->
    exists i, oseq.onth s i = Some (x,y).
  Proof.
    elim: s => //= -[hsx hsy] ts IHs.
    case: ifP => [/eqP ? [?]|_ Hassoc]; first by subst hsx hsy; exists 0.
    by case: (IHs Hassoc) => i Honth; exists i.+1.
  Qed.

End AssocOnth.
