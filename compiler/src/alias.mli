open Prog

type sub_slice_kind =
  | Exact
    (* the range is exact *)
  | Sub of Wsize.wsize
    (* the precise offset is not known, we remember that it is a subpart
       and its alignment *)

type slice = { in_var : var ; scope : E.v_scope ; range : int * int; kind : sub_slice_kind }

type alias = slice Mv.t

val normalize_var : alias -> var -> slice

val analyze_fd : (funname -> int option list) -> ('a, 'asm) Prog.func -> alias

val classes : alias -> Sv.t Mv.t

val pp_slice : Format.formatter -> slice -> unit

val pp_alias  : Format.formatter -> alias -> unit
