(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
Require Import global Utf8.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant label_kind :=
  | InternalLabel
  | ExternalLabel
.

(* ==================================================================== *)
Definition label := positive.
Bind Scope positive_scope with label.

Definition remote_label := (funname * label)%type.

(* Indirect jumps use labels encoded as pointers: we assume such an encoding exists.
  The encoding and decoding functions are parameterized by a domain:
  they are assumed to succeed on this domain only.
*)

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Section  SPEC.
  Context
    (enc: seq remote_label → remote_label → option pointer)
    (dec: seq remote_label → pointer → option remote_label).

  (* The domain should be small enough, otherwise it is not possible to associate
     a distinct word to each label. *)
  Definition small_dom (dom : seq remote_label) :=
    (Z.of_nat (size dom) <=? wbase Uptr)%Z.

  Definition decode_encode_label_t : Prop :=
    ∀ dom lbl,
      small_dom dom →
      lbl \in dom →
      obind (dec dom) (enc dom lbl) = Some lbl.

End  SPEC.

Section CONSISTENCY.
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
    rewrite -has_pred1 => /dup[] => lbl_in_dom.
    rewrite has_find => /= /dup[] /ltP found -> /=.
    rewrite wunsigned_repr_small; last first.
    - move: (find _ _) (size _) small_dom found => n m; Lia.lia.
    rewrite Nat2Z.id oseq.onth_nth.
    rewrite (nth_map lbl); last exact/ltP.
    by have /eqP -> := nth_find lbl lbl_in_dom.
  Qed.

End CONSISTENCY.

Parameter encode_label : seq remote_label → remote_label → option pointer.
Parameter decode_label : seq remote_label → pointer → option remote_label.

Axiom decode_encode_label : decode_encode_label_t encode_label decode_label.

Lemma encode_label_dom :
  ∀ dom lbl, small_dom dom → lbl \in dom → encode_label dom lbl ≠ None.
Proof.
  move=> dom lbl small_dom hmem.
  have := decode_encode_label small_dom hmem.
  by case: encode_label.
Qed.

Definition rencode_label
  (lbls : seq remote_label) (lbl : remote_label) : exec (word Uptr) :=
  o2r ErrType (encode_label lbls lbl).

Definition rdecode_label
  (lbls : seq remote_label) (w : word Uptr) : exec remote_label :=
  o2r ErrType (decode_label lbls w).

End WITH_POINTER_DATA.
