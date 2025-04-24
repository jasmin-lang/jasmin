open PrintASM

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_printer = {
  headers : asm_element list;
  data_segment_header : asm_element list;
  function_header : asm_element list;
  function_tail : asm_element list;
  pp_instr_r :
    CoreIdent.Name.t ->
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_i_r ->
    asm_element list;
}
(** Record asm_printer : This record defines the interface for generating
    assembly code for a target architecture. You need to provide the header,
    function header, function tail and instruction generation function. *)

val asm_of_prog :
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_printer ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_prog ->
  asm_element list
