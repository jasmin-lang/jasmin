type amodel =
  | ArrayOld
  | WArray
  | BArray

val ty_expr : (Expr.sop1, Expr.sop2) Prog.expr -> Prog.ty
val ty_lval : ('sop1, 'sop2) Prog.lval -> Prog.ty
val extract :
  (Expr.sop1, Expr.sop2, 'info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Utils.model ->
  amodel ->
  string list ->
  string option ->
  Format.formatter ->
  unit
