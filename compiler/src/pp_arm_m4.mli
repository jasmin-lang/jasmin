val mangle : string -> string

(* [pp_instr tbl fn fmt i] prints an ARMv7 assembly instruction. *)
val print_instr :
  Conv.coq_tbl
  -> string (* Current function name. *)
  -> Format.formatter
  -> ( Arm_decl.register
     , Arm_decl.__
     , Arm_decl.__
     , Arm_decl.rflag
     , Arm_decl.condt
     , Arm_instr_decl.arm_op )
     Arch_decl.asm_i
  -> unit

val print_prog :
  Conv.coq_tbl -> Format.formatter -> Arm_sem.arm_prog -> unit
