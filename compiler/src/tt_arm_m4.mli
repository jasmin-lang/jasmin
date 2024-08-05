val tt_prim :
  (string -> exn)
  -> (string * 'a Sopn.prim_constructor) list
  -> string
  -> _ option
  -> 'a
