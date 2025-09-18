type amodel =
  | ArrayOld
  | WArray
  | BArray

val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract :
  ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  (Utils.model * Utils.decl_model) ->
  amodel ->
  string list ->
  string option ->
  Format.formatter ->
  unit
