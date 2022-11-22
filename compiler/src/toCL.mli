val extract :
('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.asmOp ->
Stdlib__format.formatter ->
('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.asm_extra ->
(('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op, Stdlib__obj.t,
 Stdlib__obj.t)
Expr._prog ->
('a, 'b, 'c, 'd, 'e, 'f, 'g, 'i, 'j) Arch_params.architecture_params ->
(('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op, 'i, 'j)
Compiler.compiler_params ->
BinNums.positive list ->
BinNums.positive list ->
Conv.coq_tbl ->
('a, 'b, 'c, 'd, 'e) Arch_decl.calling_convention ->
string list ->
(Compiler_util.pp_error_loc,
 ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Linear.lprog)
Utils0.result
