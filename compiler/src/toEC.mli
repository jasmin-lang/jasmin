type amodel =
  | ArrayOld
  | WArray
  | BArray

val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract :
  ('info, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('asm_op, 'extra_op) Arch_extra.extended_op_gen Sopn.asmOp ->
  Utils.model ->
  amodel ->
  string list ->
  string option ->
  Format.formatter ->
  unit
