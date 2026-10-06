From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

From Coq Require Import ZArith String.
Require Import utils word.

(* -------------------------------------------------------------------- *)
(* Valid immediates checks. *)

#[only(eqbOK)] derive
Variant expand_immediate_kind :=
| EI_none
| EI_byte
| EI_pattern
| EI_shift.

HB.instance Definition _ := hasDecEq.Build expand_immediate_kind expand_immediate_kind_eqb_OK.

Definition z_to_bytes (n : Z) : Z * Z * Z * Z :=
  let '(n, b0) := Z.div_eucl n 256 in
  let '(n, b1) := Z.div_eucl n 256 in
  let '(n, b2) := Z.div_eucl n 256 in
  let b3 := (n mod 256)%Z in
  (b3, b2, b1, b0).

(* An immediate of the pattern kind has the shape [bbbb], [0b0b], or [b0b0],
   where [b] is a byte. *)
Definition is_ei_pattern (n : Z) : bool :=
  let '(b3, b2, b1, b0) := z_to_bytes n in
  [|| [&& b3 == b0, b2 == b0 & b1 == b0 ]
    , [&& b3 == 0%Z, b2 == b0 & b1 == 0%Z ]
    | [&& b3 == b1, b2 == 0%Z & b0 == 0%Z ]
  ].

(* An immediate of the shift kind has the shape [0...01xxxxxxx0...0] where the
   number of suffix zeroes is at least one.
   Here we assume that last part, i.e. that [n] is larger than 2 (if it were
   not, we would have caught it in the ETI_byte case). *)
Definition is_ei_shift (n : Z) : bool :=
  (* Find where the first set bit and move 7 bits further. *)
  let byte_end := (Z.log2 n - 7)%Z in
  (* Check if any bit after the byte is one. *)
  Z.rem n (Z.pow 2 byte_end) == 0%Z.

Definition ei_kind (n : Z) : expand_immediate_kind :=
  if [&& 0 <=? n & n <? 256 ]%Z then EI_byte
  else if is_ei_pattern n then EI_pattern
  else if is_ei_shift n then EI_shift
  else EI_none.

#[only(eqbOK)] derive
Variant wencoding :=
  | WE_allowed of bool (* false this encoding is not allowed *)
  | W12_encoding
  | W16_encoding.

HB.instance Definition _ := hasDecEq.Build wencoding wencoding_eqb_OK.

#[only(eqbOK)] derive
Record expected_wencoding :=
  { on_shift : wencoding;
    on_none  : wencoding; }.

HB.instance Definition _ := hasDecEq.Build expected_wencoding expected_wencoding_eqb_OK.

Definition is_w12_encoding (z : Z) : bool := (z <? Z.pow 2 12)%Z.
Definition is_w16_encoding (z : Z) : bool := (z <? Z.pow 2 16)%Z.

Definition check_wencoding we z :=
  match we with
  | WE_allowed b => b
  | W12_encoding => is_w12_encoding z
  | W16_encoding => is_w16_encoding z
  end.

Definition check_ei_kind ewe sz (w: word sz) :=
  let z := wunsigned w in
  match ei_kind z with
  | EI_pattern | EI_byte => true
  | EI_shift => check_wencoding (on_shift ewe) z
  | EI_none => check_wencoding (on_none ewe) z
  end.

Definition string_of_ew ew :=
  match ew with
  | WE_allowed b => if b then "allowed"%string else "not allowed"%string
  | W12_encoding => "W12"%string
  | W16_encoding => "W16"%string
  end.

