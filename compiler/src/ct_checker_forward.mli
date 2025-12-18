open Prog
open Operators

val is_ct_op1 : sop1 -> bool
val is_ct_op2 : sop2 -> bool
val is_ct_opN : opN -> bool
val is_ct_sopn : ('asm -> bool) -> 'asm Sopn.sopn -> bool

val is_declassify : loc:Location.i_loc -> Annotations.annotations -> bool
(** Look for deprecated “declassify” annotation: returns true and warns if found. *)

type signature
(** Security type of a function *)

val pp_signature : Format.formatter -> signature -> unit
(** Human-readable form of a signature *)

val ty_prog :
  ('asm -> bool) ->
  infer:bool ->
  ('info, 'asm) prog ->
  Name.t list ->
  (('info, 'asm) func * signature) list * (L.t * (Format.formatter -> unit)) option
(** Type-check (for constant-time) a list of functions in the given program
  (defaults to all functions if the list is empty).

  Returns the signature of all functions that have been successfully
  type-checked and an optional error message in case of failure (type-checking
  aborts after the first error).

  When [infer] is false, checking of export functions fails unless they are correctly annotated.
*)
