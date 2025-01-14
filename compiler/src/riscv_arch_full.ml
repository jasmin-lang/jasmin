open Arch_decl
open Prog
open Riscv_decl
open Riscv_extra

module type Riscv_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, condt) calling_convention

end

module Riscv_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag =  Arch_utils.empty
  type cond = condt
  type asm_op = Riscv_instr_decl.riscv_op
  type extra_op = Riscv_extra.riscv_extra_op
  type lowering_options = Riscv_lowering.lowering_options

  let atoI = X86_arch_full.atoI riscv_decl

  let asm_e =  Riscv_extra.riscv_extra atoI
  let aparams = Riscv_params.riscv_params atoI
  let known_implicits = []

  let alloc_stack_need_extra sz =
    not (Riscv_params_core.is_arith_small (Conv.cz_of_z sz))

  (* FIXME RISCV: check if everything is ct *)
  let is_ct_asm_op (o : asm_op) =
    match o with
    | _ -> true

  let is_ct_asm_extra (o : extra_op) = true

  let is_doit_asm_op (o : asm_op) = true

  (* All of the extra ops compile into DIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) = true

end

module Riscv (Lowering_params : Riscv_input) : Arch_full.Core_arch = struct
  include Riscv_core
  include Lowering_params

  let lowering_opt = ()

  let not_saved_stack = (Riscv_params.riscv_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_riscv.print_prog

  let callstyle = Arch_full.ByReg { call = Some RA; return = true }
end
