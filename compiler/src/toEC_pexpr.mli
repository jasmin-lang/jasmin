val ty_expr : Prog.pexpr -> Prog.pty
val ty_lval : Prog.plval -> Prog.pty

val extract_modular :
  (Prog.pexpr_, int, 'info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Mprog.module_summary list ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Utils.model ->
  ToEC.amodel ->
  string list ->
  string option ->
  Format.formatter list ->
  unit