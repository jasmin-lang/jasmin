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

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq ssralg.
From mathcomp Require Import word_ssrZ.
Require Import utils word.
Import Utf8 ZArith.

#[local] Open Scope word_scope.

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

