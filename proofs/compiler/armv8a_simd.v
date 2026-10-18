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
Require Import utils word.
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
