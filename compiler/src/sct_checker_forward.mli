open Prog

type ty_fun

val pp_funty : Format.formatter -> Name.t * ty_fun -> unit
val ty_prog : ('info, 'asm) prog -> Name.t list -> (Name.t * ty_fun) list

val compile_infer_msf :
  ('info, 'asm) prog -> (Slh_ops.slh_t list * Slh_ops.slh_t list) Hf.t
