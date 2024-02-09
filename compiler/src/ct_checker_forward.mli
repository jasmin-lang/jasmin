open Prog

val is_ct_op1 : Expr.sop1 -> bool
val is_ct_op2 : Expr.sop2 -> bool
val is_ct_opN : Expr.opN -> bool
val is_ct_sopn : ('asm -> bool) -> 'asm Sopn.sopn -> bool


type signature
(** Security type of a function *)

val pp_signature : _ prog -> Format.formatter -> funname * signature -> unit
(** Human-readable form of a signature *)

val ty_prog :
  ('asm -> bool) ->
  infer:bool ->
  (_, 'asm) prog ->
  Name.t list ->
  (funname * signature) list * (L.t * (Format.formatter -> unit)) option
(** Type-check (for constant-time) a list of functions in the given program
  (defaults to all functions if the list is empty).

  Returns the signature of all functions that have been successfully
  type-checked and an optional error message in case of failure (type-checking
  aborts after the first error).

  When [infer] is false, checking of export functions fails unless they are correctly annotated.
*)
