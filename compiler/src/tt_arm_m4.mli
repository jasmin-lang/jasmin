module L = Location
module S = Syntax

val tt_prim :
  (string * 'a Sopn.prim_constructor) list
  -> string
  -> S.size_annotation
  -> 'a option
