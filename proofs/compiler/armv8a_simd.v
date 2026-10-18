(* ARMv8-A (AArch64) Advanced SIMD semantics.

   Word-level functions used by the instruction descriptions of
   armv8a_instr_decl.v for the SIMD&FP register file. Each function is our
   transcription of the operational pseudocode of the Arm Architecture
   Reference Manual (ARM DDI 0487 M.d): of an instruction,
   cited beside the description that uses the function, or of a shared
   pseudocode function, cited here. Like the instruction semantics, they
   are trusted: nothing here is proved against the architecture.

   Conventions. A 128-bit register is a [u128]. Its elements of [ve] bits
   are [split_vec ve w], element 0 first: element [e] is bits
   [e*ve + ve - 1 .. e*ve]. Results are rebuilt with [make_vec U128]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq div ssralg.
From mathcomp Require Import word_ssrZ.
Require Import utils word sha256.
Import Utf8 ZArith.

#[local] Open Scope word_scope.

(* -------------------------------------------------------------------- *)
(* Element access. A register with one element replaced is [wpinsr], and a
   register with the same element everywhere is [wpbroadcast U128]
   (word.v). *)

(* The [i]-th [ve]-bit element of [w], counting from the least significant
   end; 0 past the last element. *)
Definition velem_at (ve : wsize) (w : u128) (i : nat) : word ve :=
  nth (wrepr ve 0) (split_vec ve w) i.

(* The number of [ve]-bit elements of a 128-bit register. *)
Definition velems (ve : wsize) : nat := (U128 %/ ve)%nat.

(* An immediate element index, as a natural number. *)
Definition vindex (i : u8) : nat := Z.to_nat (wunsigned i).

(* -------------------------------------------------------------------- *)
(* Element-wise shifts and inserts. *)

(* One element of SRI: [n] shifted right by [sh], with the top [sh] bits
   taken from [d]. *)
Definition vsri_elem {ve : wsize} (sh : Z) (d n : word ve) : word ve :=
  wor (wand d (wnot (wshr (-1)%R sh))) (wshr n sh).

(* One element of SLI: [n] shifted left by [sh], with the low [sh] bits
   taken from [d]. *)
Definition vsli_elem {ve : wsize} (sh : Z) (d n : word ve) : word ve :=
  wor (wand d (wnot (wshl (-1)%R sh))) (wshl n sh).

(* -------------------------------------------------------------------- *)
(* Permutations. *)

(* The [ve]-bit elements of a container in reverse order (Reverse,
   J1.4.3.22, p. J1-16525). *)
Definition vrev_elems (ve : wsize) {cs : wsize} (c : word cs) : word cs :=
  make_vec cs (rev (split_vec ve c)).

(* [part] is 0 for TRN1/ZIP1/UZP1 and 1 for TRN2/ZIP2/UZP2. *)
Definition vtrn (ve : wsize) (part : nat) (a b : u128) : u128 :=
  let pairs := (velems ve %/ 2)%nat in
  make_vec U128
    (flatten [seq [:: velem_at ve a (2 * p + part); velem_at ve b (2 * p + part) ]
             | p <- iota 0 pairs ]).

Definition vzip (ve : wsize) (part : nat) (a b : u128) : u128 :=
  let pairs := (velems ve %/ 2)%nat in
  let base := (part * pairs)%nat in
  make_vec U128
    (flatten [seq [:: velem_at ve a (base + p); velem_at ve b (base + p) ]
             | p <- iota 0 pairs ]).

Definition vuzp (ve : wsize) (part : nat) (a b : u128) : u128 :=
  let zipped := split_vec ve a ++ split_vec ve b in
  make_vec U128
    [seq nth (wrepr ve 0) zipped (2 * e + part) | e <- iota 0 (velems ve) ].

(* EXT: bytes [index .. index + 15] of the 32-byte value whose bytes 0..15
   are [lo] and bytes 16..31 are [hi]. *)
Definition vext (lo hi : u128) (index : nat) : u128 :=
  zero_extend U128 (wshr (make_vec U256 [:: lo; hi ]) (8 * Z.of_nat index)).

(* -------------------------------------------------------------------- *)
(* SHA-256 (FEAT_SHA256). The helper functions are those of sha256.v:
   - [Σ₀] and [Σ₁] are SHA256hashSIGMA0 and SHA256hashSIGMA1
     ([J1.4.3.49 SHA256hashSIGMA0] and [J1.4.3.50 SHA256hashSIGMA1],
     ARM DDI 0487 M.d, p. J1-16537);
   - [σ₀] and [σ₁] are the functions that SHA256SU0 and SHA256SU1 apply to
     each element;
   - [ch] and [maj] are SHAchoose and SHAmajority at 32 bits
     ([J1.4.3.51 SHAchoose] and [J1.4.3.52 SHAmajority], ARM DDI 0487 M.d,
     p. J1-16537), written as in FIPS 180-4; armv8a_simd_lemmas.v proves
     that they are equal to the formulas of the manual. *)

(* [J1.4.3.52 SHAmajority] ARM DDI 0487 M.d, p. J1-16537
   The bitwise majority of [x], [y] and [z], for 32- and 64-bit words;
   SHA512H2 uses it at 64 bits. *)
Definition sha_majority {ws : wsize} (x y z : word ws) : word ws :=
  wor (wand x y) (wand (wor x y) z).

Notation elems4 := (u32 * u32 * u32 * u32)%type.

Definition elems4_of (w : u128) : elems4 :=
  (velem_at U32 w 0, velem_at U32 w 1, velem_at U32 w 2, velem_at U32 w 3).

Definition u128_of_elems4 (l : elems4) : u128 :=
  let '(l0, l1, l2, l3) := l in make_vec U128 [:: l0; l1; l2; l3 ].

(* One iteration of the loop of SHA256hash. [x] and [y] are given element
   0 first. The iteration ends by rotating the 256-bit value formed by [y]
   above [x] left by one 32-bit element, which moves the top element of [y]
   to element 0 of [x] and the top element of [x] to element 0 of [y]. *)
Definition sha256hash_step (xy : elems4 * elems4) (wk : u32) : elems4 * elems4 :=
  let '((x0, x1, x2, x3), (y0, y1, y2, y3)) := xy in
  let t := y3 + Σ₁ y0 + ch y0 y1 y2 + wk in
  let x3' := t + x3 in
  let y3' := t + Σ₀ x0 + maj x0 x1 x2 in
  ((y3', x0, x1, x2), (x3', y0, y1, y2)).

(* [J1.4.3.48 SHA256hash] ARM DDI 0487 M.d, p. J1-16536
   Four iterations of [sha256hash_step], one per 32-bit element of [w] in
   order, starting from [x] and [y]; the result is the final [x] when
   [part1] holds and the final [y] otherwise. *)
Definition sha256hash (x y w : u128) (part1 : bool) : u128 :=
  let '(x', y') := foldl sha256hash_step (elems4_of x, elems4_of y) (split_vec U32 w) in
  u128_of_elems4 (if part1 then x' else y').

(* SHA256SU0 Vd.4S, Vn.4S with [op1] = Vd and [op2] = Vn: element [e] is
   op1[e] plus [σ₀] of element [e] of the sequence op1[1], op1[2], op1[3],
   op2[0]. *)
Definition sha256su0 (op1 op2 : u128) : u128 :=
  let t := [:: velem_at U32 op1 1; velem_at U32 op1 2; velem_at U32 op1 3;
               velem_at U32 op2 0 ] in
  make_vec U128
    (map2 (fun te o1 => σ₀ te + o1) t (split_vec U32 op1)).

(* SHA256SU1 Vd.4S, Vn.4S, Vm.4S with [op1] = Vd, [op2] = Vn, [op3] = Vm,
   and [t0] the sequence op2[1], op2[2], op2[3], op3[0]: element [e] is
   op1[e] + t0[e] plus [σ₁] of op3[e + 2] for e = 0, 1, and of result
   element e - 2 for e = 2, 3. *)
Definition sha256su1 (op1 op2 op3 : u128) : u128 :=
  let o1 := velem_at U32 op1 in
  let t0 := [:: velem_at U32 op2 1; velem_at U32 op2 2; velem_at U32 op2 3;
                velem_at U32 op3 0 ] in
  let t0e := nth 0%R t0 in
  let r0 := σ₁ (velem_at U32 op3 2) + o1 0%N + t0e 0%N in
  let r1 := σ₁ (velem_at U32 op3 3) + o1 1%N + t0e 1%N in
  let r2 := σ₁ r0 + o1 2%N + t0e 2%N in
  let r3 := σ₁ r1 + o1 3%N + t0e 3%N in
  make_vec U128 [:: r0; r1; r2; r3 ].

(* -------------------------------------------------------------------- *)
(* SHA-512 (FEAT_SHA512). Element 0 is [w[63:0]], element 1 [w[127:64]]. *)

(* MSigma1 and NSigma0 of the SHA512H and SHA512H2 pseudocode, and sig0
   and sig1 of SHA512SU0 and SHA512SU1, where the right shift by 7 or 6 is
   written as a concatenation with zeros. *)
Definition sha512_Sigma1 (x : u64) : u64 :=
  wxor (wxor (wror x 14) (wror x 18)) (wror x 41).

Definition sha512_Sigma0 (x : u64) : u64 :=
  wxor (wxor (wror x 28) (wror x 34)) (wror x 39).

Definition sha512_sigma0 (x : u64) : u64 :=
  wxor (wxor (wror x 1) (wror x 8)) (wshr x 7).

Definition sha512_sigma1 (x : u64) : u64 :=
  wxor (wxor (wror x 19) (wror x 61)) (wshr x 6).

(* SHA512H Qd, Qn, Vm.2D with [x] = Vn, [y] = Vm and [w] = Vd. *)
Definition sha512h (w x y : u128) : u128 :=
  let x0 := velem_at U64 x 0 in let x1 := velem_at U64 x 1 in
  let y0 := velem_at U64 y 0 in let y1 := velem_at U64 y 1 in
  let w0 := velem_at U64 w 0 in let w1 := velem_at U64 w 1 in
  let v1 := wxor (wand y1 x0) (wand (wnot y1) x1) in
  let v1 := v1 + sha512_Sigma1 y1 + w1 in
  let tmp := v1 + y0 in
  let v0 := wxor (wand tmp y1) (wand (wnot tmp) x0) in
  let v0 := v0 + sha512_Sigma1 tmp + w0 in
  make_vec U128 [:: v0; v1 ].

(* SHA512H2 Qd, Qn, Vm.2D with [x] = Vn, [y] = Vm and [w] = Vd. *)
Definition sha512h2 (w x y : u128) : u128 :=
  let x0 := velem_at U64 x 0 in
  let y0 := velem_at U64 y 0 in let y1 := velem_at U64 y 1 in
  let w0 := velem_at U64 w 0 in let w1 := velem_at U64 w 1 in
  let v1 := sha_majority x0 y1 y0 in
  let v1 := v1 + sha512_Sigma0 y0 + w1 in
  let v0 := sha_majority v1 y0 y1 in
  let v0 := v0 + sha512_Sigma0 v1 + w0 in
  make_vec U128 [:: v0; v1 ].

(* SHA512SU0 Vd.2D, Vn.2D with [x] = Vn and [w] = Vd. *)
Definition sha512su0 (w x : u128) : u128 :=
  let x0 := velem_at U64 x 0 in
  let w0 := velem_at U64 w 0 in let w1 := velem_at U64 w 1 in
  make_vec U128 [:: w0 + sha512_sigma0 w1; w1 + sha512_sigma0 x0 ].

(* SHA512SU1 Vd.2D, Vn.2D, Vm.2D with [x] = Vn, [y] = Vm and [w] = Vd. *)
Definition sha512su1 (w x y : u128) : u128 :=
  let x0 := velem_at U64 x 0 in let x1 := velem_at U64 x 1 in
  let y0 := velem_at U64 y 0 in let y1 := velem_at U64 y 1 in
  let w0 := velem_at U64 w 0 in let w1 := velem_at U64 w 1 in
  make_vec U128 [:: w0 + sha512_sigma1 x0 + y0; w1 + sha512_sigma1 x1 + y1 ].
