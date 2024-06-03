From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From Coq Require Import ZArith.

Require Import
  utils
  word.
Require Import arm_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Definition u32_to_bytes (w : u32) : u8 * u8 * u8 * u8 :=
  ( word.subword 24 8 w
  , word.subword 16 8 w
  , word.subword 8 8 w
  , word.subword 0 8 w
  ).

(* This is the actual definition of [EI_byte] and [EI_pattern]. *)
Definition u32_is_expandable (w : u32) : bool :=
  let '(b3, b2, b1, b0) := u32_to_bytes w in
  [|| [&& b3 == 0, b2 == 0 & b1 == 0 ]
    , [&& b3 == b0, b2 == b0 & b1 == b0 ]
    , [&& b3 == 0, b2 == b0 & b1 == 0 ]
    | [&& b3 == b1, b2 == 0 & b0 == 0 ]
  ]%R.

Lemma z_to_bytes_u32_to_bytes w :
  let '(b3, b2, b1, b0) := u32_to_bytes w in
  let '(b3', b2', b1', b0') := z_to_bytes (wunsigned w) in
  [/\ b3' = wunsigned b3
    , b2' = wunsigned b2
    , b1' = wunsigned b1
    & b0' = wunsigned b0
  ].
Proof.
  rewrite /z_to_bytes /u32_to_bytes.
  case: Z.div_eucl (Z_div_mod (wunsigned w) 256 refl_equal) => [q0 b] [hw hb].
  case: Z.div_eucl (Z_div_mod q0 256 refl_equal) => [q1 b1'] [hq1 hb1'];
    subst q0.
  case: Z.div_eucl (Z_div_mod q1 256 refl_equal) => [q2 b2'] [hq2 hb2'];
    subst q1.

  rewrite /wunsigned /word.subword -!word.urepr_word !word.urepr_lsr !word.mkwordK /= -/(wunsigned w) hw {hw}.
  rewrite -/(wbase U8) -/(wbase U32).
  rewrite !Z.shiftr_div_pow2 // Z.mul_comm Z.add_comm.
  change (2 ^ 16) with (2 ^ 8 * 2 ^ 8).
  change (2 ^ 24) with (2 ^ 8 * 2 ^ 8 * 2 ^ 8).
  do 2 rewrite -Z.div_div //.
  split; last first.

  rewrite Z.div_1_r.

  all: repeat rewrite
         Z.div_add //
         Z.mul_comm
         Z.add_comm
         (Z.div_small _ 256) //
         Z.add_0_r
         Z.add_comm.

  1-3: by rewrite Z.mod_add // Z.mod_small.
  by rewrite Z.div_add // Z.div_small.
Qed.
