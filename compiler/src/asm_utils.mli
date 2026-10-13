val global_datas_label : string
val pp_syscall : 'a Syscall_t.syscall_t -> string
val string_of_label : string -> Label.label -> string
val pp_remote_label : Label.remote_label -> string
val mangle : string -> string

(** The target of a call on the ARM targets: the symbol of the callee when
    the functions are laid out in sections of their own (a cross-section
    call needs a relocation against a typed symbol), the assembler-local
    label heading its body otherwise. *)
val pp_call_target : Label.remote_label -> string

(** ".text.<name>" section holding the code of one function. *)
val text_section : string -> PrintASM.asm_element

val format_glob_data :
  Word0.word list ->
  ((Var0.Var.var * Wsize.wsize) * BinNums.coq_Z) list ->
  PrintASM.asm_element list

val hash_to_string : ('a -> string) -> 'a -> string
val pp_imm : string -> Z.t -> string
val pp_rip_address : Word0.word -> string
val pp_register : ('reg, _, _, _, _) Arch_decl.arch_decl -> 'reg -> string

type parsed_reg_address = {
  base : string;
  displacement : string option;
  offset : string option;
  scale : string option;
}

val parse_reg_address :
  ('reg, _, _, _, _) Arch_decl.arch_decl ->
  ('reg, _, _, _, _) Arch_decl.reg_address ->
  parsed_reg_address

val declassify_mem :
   ('a, 'b, 'c, 'd, 'e) Arch_decl.arch_decl ->
   BinNums.coq_Z ->
   ('a, 'f, 'g, 'h, 'i) Arch_decl.address ->
   PrintASM.asm

val declassify_val : (Type.ltype -> 'a -> string) -> Type.ltype -> 'a -> PrintASM.asm

