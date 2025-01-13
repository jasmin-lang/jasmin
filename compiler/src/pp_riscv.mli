val mangle : string -> string

val print_instr :
  string (* Current function name. *) ->
  Format.formatter ->
  ( Riscv_decl.register,
    Arch_utils.empty,
    Arch_utils.empty,
    Arch_utils.empty,
    Riscv_decl.condt,
    Riscv_instr_decl.riscv_op )
  Arch_decl.asm_i_r ->
  unit

val print_prog : Format.formatter -> Riscv_instr_decl.riscv_prog -> unit
