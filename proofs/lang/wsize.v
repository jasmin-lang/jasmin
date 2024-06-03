(* ** Machine word *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype fintype.
Require Import strings ZArith utils.
Import Utf8.
Import word_ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------- *)
Variant wsize :=
  | U8
  | U16
  | U32
  | U64
  | U128
  | U256.

(* Size in bits of the elements of a vector. *)
Variant velem := VE8 | VE16 | VE32 | VE64.

Coercion wsize_of_velem (ve: velem) : wsize :=
  match ve with
  | VE8 => U8
  | VE16 => U16
  | VE32 => U32
  | VE64 => U64
  end.

(* Size in bits of the elements of a pack. *)
Variant pelem :=
| PE1 | PE2 | PE4 | PE8 | PE16 | PE32 | PE64 | PE128.

Variant signedness :=
  | Signed
  | Unsigned.

(* -------------------------------------------------------------------- *)
Scheme Equality for wsize.

Lemma wsize_axiom : Equality.axiom wsize_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_wsize_dec_bl internal_wsize_dec_lb).
Qed.

Definition wsize_eqMixin     := Equality.Mixin wsize_axiom.
Canonical  wsize_eqType      := Eval hnf in EqType wsize wsize_eqMixin.

Definition wsizes :=
  [:: U8 ; U16 ; U32 ; U64 ; U128 ; U256 ].

Lemma wsize_fin_axiom : Finite.axiom wsizes.
Proof. by case. Qed.

(* ** Comparison
 * -------------------------------------------------------------------- *)
Definition wsize_cmp s s' :=
  match s, s' with
  | U8, U8 => Eq
  | U8, (U16 | U32 | U64 | U128 | U256)  => Lt
  | U16, U8 => Gt
  | U16, U16 => Eq
  | U16, (U32 | U64 | U128 | U256) => Lt
  | U32, (U8 | U16) => Gt
  | U32, U32 => Eq
  | U32, (U64 | U128 | U256) => Lt
  | U64, (U8 | U16 | U32) => Gt
  | U64, U64 => Eq
  | U64, ( U128 | U256) => Lt
  | U128, (U8 | U16 | U32 | U64) => Gt
  | U128, U128 => Eq
  | U128, U256 => Lt
  | U256, (U8 | U16 | U32 | U64 | U128) => Gt
  | U256, U256 => Eq
  end.

#[export]
Instance wsizeO : Cmp wsize_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> [] [] [] //= ? [].
  by move=> [] [].
Qed.

Lemma wsize_le_U8 s: (U8 <= s)%CMP.
Proof. by case: s. Qed.

Lemma wsize_ge_U256 s: (s <= U256)%CMP.
Proof. by case s. Qed.

#[global]Hint Resolve wsize_le_U8 wsize_ge_U256: core.

(* -------------------------------------------------------------------- *)
Definition check_size_8_64 sz := assert (sz ≤ U64)%CMP ErrType.
Definition check_size_8_32 sz := assert (sz ≤ U32)%CMP ErrType.
Definition check_size_16_32 sz := assert ((U16 ≤ sz) && (sz ≤ U32))%CMP ErrType.
Definition check_size_16_64 sz := assert ((U16 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_32_64 sz := assert ((U32 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_128_256 sz := assert ((U128 ≤ sz) && (sz ≤ U256))%CMP ErrType.

Lemma wsize_nle_u64_check_128_256 sz :
  (sz ≤ U64)%CMP = false →
  check_size_128_256 sz = ok tt.
Proof. by case: sz. Qed.

(* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------- *)
Definition string_of_wsize (sz: wsize) : string :=
  match sz with
  | U8 => "8"
  | U16 => "16"
  | U32 => "32"
  | U64 => "64"
  | U128 => "128"
  | U256 => "256"
  end.

Definition string_of_ve_sz (ve:velem) (sz:wsize) : string :=
  match ve, sz with
  | VE8, U16 => "2u8"
  | VE8, U32 => "4u8"
  | VE16, U32 => "2u16"
  | VE8, U64 => "8u8"
  | VE16, U64 => "4u16"
  | VE32, U64 => "2u32"
  | VE8 , U128 => "16u8"
  | VE16, U128 => "8u16"
  | VE32, U128 => "4u32"
  | VE64, U128 => "2u64"
  | VE8 , U256 => "32u8"
  | VE16, U256 => "16u16"
  | VE32, U256 => "8u32"
  | VE64, U256 => "4u64"
  | _,    _    => "ERROR: please repport"
  end.

Definition pp_s (s: string) (_: unit) : string := s.

Definition pp_sz (s: string) (sz: wsize) (_: unit) : string := 
  s ++ "_" ++ string_of_wsize sz.

Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string := 
  s ++ "_" ++ string_of_ve_sz ve sz.

Definition pp_ve_sz_ve_sz (s: string) (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (_: unit) : string :=
  s ++ "_" ++ string_of_ve_sz ve sz ++ "_" ++ string_of_ve_sz ve' sz'.

Definition pp_sz_sz (s: string) (sign:bool) (sz sz': wsize) (_: unit) : string :=
  s ++ "_u" ++ string_of_wsize sz ++ (if sign then "s" else "u")%string ++ string_of_wsize sz'.

(* -------------------------------------------------------------------- *)
Variant reg_kind : Type :=
| Normal
| Extra.

Variant writable : Type := Constant | Writable.

Variant reference : Type := Direct | Pointer of writable.

Variant v_kind :=
| Const            (* global parameter  *)
| Stack of reference (* stack variable    *)
| Reg   of reg_kind * reference (* register variable *)
| Inline           (* inline variable   *)
| Global           (* global (in memory) constant *)
.

(* -------------------------------------------------------------------- *)
Variant safe_cond :=
  | X86Division of wsize & signedness (* this is a division instruction, two words by one word; result must fit in an single word *)
  | InRange of wsize & Z & Z & nat (* the nth argument must be in the given range *)
  | AllInit of wsize & positive & nat.         (* the nth argument of is an array ws[p] where all ceil are initialized *)


(* -------------------------------------------------------------------- *)
Class PointerData := {
  Uptr : wsize;
}.

(* -------------------------------------------------------------------- *)
Class MSFsize :=
  {
    msf_size : wsize;
  }.
