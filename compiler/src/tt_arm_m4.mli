module L = Location
module S = Syntax

val tt_prim :
  (string * 'a Sopn.prim_constructor) list
  -> string
  -> S.pexpr_r L.located list
  -> ('a * S.pexpr_r L.located list) option
