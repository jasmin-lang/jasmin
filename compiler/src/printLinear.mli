val pp_prog :
  ('reg, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  'info Conv.coq_tbl -> Format.formatter ->
  ('reg, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Linear.lprog ->
  unit
