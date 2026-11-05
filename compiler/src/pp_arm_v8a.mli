(* ARMv8A assembly printer *)

val print_prog :
  (CoreIdent.funname -> FInfo.f_annot) -> Format.formatter -> Armv8a_instr_decl.armv8a_prog -> unit
