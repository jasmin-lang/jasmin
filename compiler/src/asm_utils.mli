val global_datas_label : string
val pp_syscall : 'a Syscall_t.syscall_t -> string
val string_of_label : string -> Label.label -> string
val pp_remote_label : Label.remote_label -> string
val mangle : string -> string

(** Declares the functions of the unit being printed that are not exported.
    Calls to those are printed against their own symbol and not against the
    assembler-local label heading them, which is what a cross-section call
    needs. Called with the empty list when the functions are not separated
    into sections. *)
val set_local_functions : string list -> unit

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

