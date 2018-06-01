val extract : Format.formatter ->
  (Prog.var * Prog.expr) list ->
  (Prog.ty, 'a) Prog.gfunc list -> string list -> unit
