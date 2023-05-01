open Wsize
(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

(* -------------------------------------------------------------------- *)
val mangle : string -> string

(* -------------------------------------------------------------------- *)
val pp_instr :
  string -> Format.formatter ->
  (X86_decl_core.register, X86_decl_core.register_ext, X86_decl_core.xmm_register, X86_decl_core.rflag, X86_decl.condt, X86_instr_decl.x86_op) Arch_decl.asm_i ->
  unit

val pp_prog  :
  Format.formatter -> X86_instr_decl.x86_prog -> unit
