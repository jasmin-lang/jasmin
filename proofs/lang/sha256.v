From mathcomp Require Import ssreflect seq ssralg.
Require Import word.
Import Utf8 ZArith.
Import utils.

#[local] Open Scope ring_scope.

Definition σ₀ (w: u32) : u32 :=
  wxor (wror w 7) (wxor (wror w 18) (wshr w 3)).

Definition σ₁ (w: u32) : u32 :=
  wxor (wror w 17) (wxor (wror w 19) (wshr w 10)).

Definition sha256msg1 (m₁ m₂: u128) : u128 :=
  let s := split_vec VE32 m₁ in
  make_vec
    U128
    (map2
       (λ x y, x + σ₀ y)
       s
       (rcons (behead s) (zero_extend U32 m₂))).

Definition sha256msg2 (m₁ m₂: u128) : u128 :=
  let src₁ : seq u32 := split_vec VE32 m₁ in
  let src₂ : seq u32 := split_vec VE32 m₂ in
  let w14 := nth 0 src₂ 2 in
  let w15 := nth 0 src₂ 3 in
  let w16 := nth 0 src₁ 0 + σ₁ w14 in
  let w17 := nth 0 src₁ 1 + σ₁ w15 in
  let w18 := nth 0 src₁ 2 + σ₁ w16 in
  let w19 := nth 0 src₁ 3 + σ₁ w17 in
  make_vec U128 [:: w16; w17; w18; w19 ].
