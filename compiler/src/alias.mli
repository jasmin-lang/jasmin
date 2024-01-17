open Prog

type slice = { in_var : var ; scope : E.v_scope; range : Z.t * Z.t }

type alias = slice Mv.t

val normalize_var : alias -> var -> slice

val analyze_fd : (funname -> int option list) -> ('a, 'asm) func -> alias

val analyze_prog : ('info, 'asm) func list -> unit

val classes : alias -> Sv.t Mv.t

val pp_slice : Format.formatter -> slice -> unit

val pp_alias  : Format.formatter -> alias -> unit
