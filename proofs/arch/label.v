(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From Coq Require Import Utf8.
Require Import global.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

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

End CONSISTENCY.

Parameter encode_label : seq remote_label → remote_label → option pointer.
Parameter decode_label : seq remote_label → pointer → option remote_label.

Axiom decode_encode_label : decode_encode_label_t encode_label decode_label.

Definition rencode_label
  (lbls : seq remote_label) (lbl : remote_label) : exec (word Uptr) :=
  o2r ErrType (encode_label lbls lbl).

Definition rdecode_label
  (lbls : seq remote_label) (w : word Uptr) : exec remote_label :=
  o2r ErrType (decode_label lbls w).

End WITH_POINTER_DATA.
