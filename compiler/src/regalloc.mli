open Prog

val fill_in_missing_names : ('info, 'asm) Prog.func -> ('info, 'asm) Prog.func

type retaddr =
  | StackDirect
  | StackByReg of var * var option * var option
  | ByReg of var * var option

type reg_oracle_t = {
  ro_to_save : var list;
      (** The list of callee save registers that are modified by a call to the
          export function *)
  ro_rsp : var option;
      (** A register that can be used to save the rsp of export function *)
}

module type Regalloc = sig
  type extended_op

  val create_return_addresses :
    (('info, 'asm) sfundef -> Z.t) -> ('info, 'asm) sfundef list -> retaddr Hf.t
  (** Compute where the return address will be stored *)

  val renaming : (unit, extended_op) func -> (unit, extended_op) func
  val subroutine_ra_by_stack : (unit, extended_op) func -> bool

  val get_reg_oracle :
    (('info, 'asm) func -> bool) ->
    (var -> var) ->
    (funname -> Sv.t) ->
    ('info, 'asm) func ->
    reg_oracle_t
  (** Extract from the outcome of register allocation the information that is
      needed by stack-allocation. *)

  val alloc_prog :
    retaddr Hf.t ->
    ('a * (unit, extended_op) func) list ->
    (var -> var) * (funname -> Sv.t) * ('a * (unit, extended_op) func) list
  (** Returns:
      - the global renaming function
      - the set of killed registers (see note below)
      - the input function with variables turned into registers

      Note: Export functions can freely use caller-saved registers: they are not
      reported as killed. Subroutines report ALL killed registers. *)
end

module Regalloc (Arch : Arch_full.Arch) :
  Regalloc with type extended_op := (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op
