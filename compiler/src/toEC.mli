val extract : Format.formatter ->
  ((Prog.Name.t * Prog.ty) * Prog.expr) list ->
  (Prog.ty, 'a) Prog.gfunc list -> string list -> unit
