val global_datas_label : string
val pp_syscall : 'a Syscall_t.syscall_t -> string
val string_of_label : string -> Label.label -> string
val pp_remote_label : Label.remote_label -> string
val mangle : string -> string

val format_glob_data :
  Obj.t list ->
  ((Var0.Var.var * Wsize.wsize) * BinNums.coq_Z) list ->
  PrintASM.asm_element list

val hash_to_string : ('a -> string) -> 'a -> string
val pp_imm : string -> Z.t -> string
val pp_rip_address : Obj.t -> string
val pp_register : ('reg, _, _, _, _) Arch_decl.arch_decl -> 'reg -> string

type parsed_reg_adress = {
  base : string;
  displacement : string option;
  offset : string option;
  scale : string option;
}

val parse_reg_adress :
  ('reg, _, _, _, _) Arch_decl.arch_decl ->
  ('reg, _, _, _, _) Arch_decl.reg_address ->
  parsed_reg_adress
