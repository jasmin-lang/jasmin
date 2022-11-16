(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra. 
Require Import global Utf8.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* FIXME: we can certainly prove false with such a spec!!! *)
Parameter encode_label : seq remote_label → remote_label → option pointer.
Parameter decode_label : seq remote_label → pointer → option remote_label.
Axiom decode_encode_label : ∀ dom lbl, obind (decode_label dom) (encode_label dom lbl) = Some lbl.
Axiom encode_label_dom : ∀ dom lbl, lbl \in dom → encode_label dom lbl ≠ None.

End WITH_POINTER_DATA.
