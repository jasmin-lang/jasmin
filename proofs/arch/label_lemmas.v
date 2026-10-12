From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From Coq Require Import Utf8.
Require Import global.
Require Import label.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section CONSISTENCY.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

  Lemma decode_encode_label_consistent :
    ∃ enc dec, decode_encode_label_t enc dec.
  Proof.
    exists (λ dom lbl,
             let r := find (pred1 lbl) dom in
             if r < size dom
             then Some (wrepr Uptr (Z.of_nat r))
             else None).
    exists (λ dom p, oseq.onth dom (Z.to_nat (wunsigned p))).
    move => dom lbl /ZleP small_dom.
    rewrite -has_pred1 => /[dup] => lbl_in_dom.
    rewrite has_find => /= /[dup] /ltP found -> /=.
    rewrite wunsigned_repr_small; last first.
    - move: (find _ _) (size _) small_dom found => n m; Lia.lia.
    rewrite Nat2Z.id oseq.onth_nth.
    rewrite (nth_map lbl); last exact/ltP.
    by have /eqP -> := nth_find lbl lbl_in_dom.
  Qed.

End WITH_POINTER_DATA.

End CONSISTENCY.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Lemma encode_label_dom :
  ∀ dom lbl, small_dom dom → lbl \in dom → encode_label dom lbl ≠ None.
Proof.
  move=> dom lbl small_dom hmem.
  have := decode_encode_label small_dom hmem.
  by case: encode_label.
Qed.

End WITH_POINTER_DATA.
