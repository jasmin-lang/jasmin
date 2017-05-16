open Prog

module X64 : sig
  val rsp : var
  val all_registers : var list
end

val regalloc : 'i1 func -> unit func
