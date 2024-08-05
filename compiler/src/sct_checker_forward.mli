open Prog

type ty_fun

val pp_funty : Format.formatter -> Name.t * ty_fun -> unit
val ty_prog : ('asm -> bool) -> ('info, 'asm) prog -> Name.t list -> (Name.t * ty_fun) list

val compile_infer_msf :
  ('info, 'asm) prog -> (Slh_lowering.slh_t list * Slh_lowering.slh_t list) Hf.t
