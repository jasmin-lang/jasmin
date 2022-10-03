val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract :
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Format.formatter ->
  Utils.model -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Prog.prog ->
  string list -> unit

val init_use : ('info, 'asm) Prog.func list -> Prog.Sf.t * Prog.Sf.t
