open Prog

val fill_in_missing_names : 'info Prog.func -> 'info Prog.func

module X64 : sig
  val rsp : var
  val allocatables : Sv.t
  val callee_save  : Sv.t
  
  val all_registers : var list
end

val regalloc : 
  (Var0.Var.var -> var) -> bool -> 'i1 func -> unit func * Sv.t * var option * var option

val split_live_ranges : 'info func -> unit func
