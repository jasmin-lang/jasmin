open Prog

type slice = { in_var : var ; scope : E.v_scope; range : int * int }

type alias = slice Mv.t

val normalize_var : alias -> var -> slice

val analyze_fd : (funname -> int option list) -> (int, 'a) Prog.gfunc -> alias

val analyze_prog : 'info func list -> unit

val classes : alias -> Sv.t Mv.t

val pp_alias  : Format.formatter -> alias -> unit
