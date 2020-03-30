open Prog

val fill_in_missing_names : 'info Prog.func -> 'info Prog.func

module X64 : sig
  (* val rsp : var *)
  val allocatables : Sv.t
  val callee_save  : Sv.t
  
  val all_registers : var list
end

(** Returns:
  - the input function with variables turned into registers
  - the set of killed registers (see note below)
  - a free register in which the stack pointer can be saved; only when asked
  - a free register for the return address; only for subroutines

Note: Export functions can freely use caller-saved registers: they are not
reported as killed. Subroutines report ALL killed registers.

 *)
val regalloc :
  (Var0.Var.var -> var) -> bool -> 'i1 func -> unit func * Sv.t * var option * var option

val split_live_ranges : 'info func -> unit func

type reg_oracle_t = {
    ro_to_save: var list;  (* TODO: allocate them in the stack rather than push/pop *)
    ro_rsp: var option;
    ro_return_address: var option;
  }

val alloc_prog : ('a -> bool) ->
 ('a * 'info func) list -> ('a * reg_oracle_t * 'info func) list
