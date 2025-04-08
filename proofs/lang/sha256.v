From mathcomp Require Import ssreflect seq ssralg.
Require Import word.
Import Utf8 ZArith.
Import utils.

#[local] Open Scope ring_scope.

Definition ch (e f g: u32) : u32 :=
  wxor (wand e f) (wand (wnot e) g).

Definition maj (a b c: u32) : u32 :=
  wxor (wand a b) (wxor (wand a c) (wand b c)).

Definition Σ₀ (a: u32) : u32 :=
  wxor (wror a 2) (wxor (wror a 13) (wror a 22)).

Definition Σ₁ (e: u32) : u32 :=
  wxor (wror e 6) (wxor (wror e 11) (wror e 25)).

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

Definition sha256rnds2 (x y z: u128) : u128 :=
  let x : seq u32 := split_vec VE32 x in
  let y : seq u32 := split_vec VE32 y in
  let z : seq u32 := split_vec VE32 z in
  if (x, y, z) is ([:: h₀; g₀; d₀; c₀ ], [:: f₀; e₀; b₀; a₀ ], [:: wk₀; wk₁; _; _])
  then
    let t₀ := ch e₀ f₀ g₀ + Σ₁ e₀ + wk₀ + h₀ in
    let a₁ := t₀ + maj a₀ b₀ c₀ + Σ₀ a₀ in
    let e₁ := t₀ + d₀ in
    let t₁ := ch e₁ e₀ f₀ + Σ₁ e₁ + wk₁ + g₀ in
    let a₂ := t₁ + maj a₁ a₀ b₀ + Σ₀ a₁ in
    let e₂ := t₁ + c₀ in
    make_vec U128 [:: e₁; e₂; a₁; a₂ ]
  else 0 (* absurd case *).
