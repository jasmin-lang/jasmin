open Wsize
(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

val print_prog  :
  (CoreIdent.funname -> FInfo.f_annot) -> Format.formatter -> X86_instr_decl.x86_prog -> unit
