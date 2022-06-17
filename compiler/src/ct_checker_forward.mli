open Prog

type signature
(** Security type of a function *)

val pp_signature : Format.formatter -> funname * signature -> unit
(** Human-readable form of a signature *)

val ty_prog :
  infer:bool -> ('info, 'asm) prog -> Name.t list -> (funname * signature) list
