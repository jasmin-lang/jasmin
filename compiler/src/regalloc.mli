open Prog

val fill_in_missing_names : ('info, 'asm) Prog.func -> ('info, 'asm) Prog.func

type retaddr = 
  | StackDirect
  | StackByReg of var * var option
  | ByReg of var * var option

type reg_oracle_t = {
    ro_to_save: var list;  (* TODO: allocate them in the stack rather than push/pop *)
    ro_rsp: var option;
    ro_return_address: retaddr;
  }

module type Regalloc = sig
  type extended_op

  val split_live_ranges : (unit, extended_op) func -> (unit, extended_op) func
  val renaming : (unit, extended_op) func -> (unit, extended_op) func
  val remove_phi_nodes : (unit, extended_op) func -> (unit, extended_op) func

  val subroutine_ra_by_stack : (unit, extended_op) func -> bool


  (** Returns:
    - the input function with variables turned into registers
    - the set of killed registers (see note below)
    - a free register in which the stack pointer can be saved; only when asked
    - a free register for the return address; only for subroutines

  Note: Export functions can freely use caller-saved registers: they are not
  reported as killed. Subroutines report ALL killed registers.

   *)
  val alloc_prog :
    (Var0.Var.var -> var) ->
    ((unit, extended_op) func -> 'a -> bool) ->
    ((unit, extended_op) func -> 'a -> Z.t) ->
    ('a * (unit, extended_op) func) list ->
    ('a * reg_oracle_t * (unit, extended_op) func) list
end

module Regalloc (Arch : Arch_full.Arch) :
  Regalloc with type extended_op := (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op
