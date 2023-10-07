open Prog

type signature
(** Speculative Security type of a function *)

val pp_signature : _ prog -> Format.formatter -> funname * signature -> unit

val ty_prog :
  infer:bool ->
  _ prog ->
  Name.t list ->
  (funname * signature) list * (L.t * (Format.formatter -> unit)) option
(** Type-check (for speculative constant-time) a list of functions in the given program
  (defaults to all functions if the list is empty).

  Returns the signature of all functions that have been successfully
  type-checked and an optional error message in case of failure (type-checking
  aborts after the first error).

  When [infer] is false, checking of export functions fails unless they are correctly annotated.
*)

val compile_infer_msf :
  ('info, 'asm) prog -> (Slh_lowering.slh_t list * Slh_lowering.slh_t list) Hf.t
(** Internal function for the compiler, does not provide any security guaranty *)
