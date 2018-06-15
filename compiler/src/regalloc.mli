open Prog

val fill_in_missing_names : 'info Prog.func -> 'info Prog.func

module X64 : sig
  val rsp : var
  val all_registers : var list
end

val regalloc : (Var0.Var.var -> var) -> 'i1 func -> unit func

val split_live_ranges : 'info func -> unit func
