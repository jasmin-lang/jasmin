open Arch_extra
open Prog

module type Core_arch = sig
  type reg
  type xreg
  type rflag
  type cond
  type asm_op
  type extra_op
  type fresh_vars
  type lowering_options

  val asm_e : (reg, xreg, rflag, cond, asm_op, extra_op) asm_extra
  val aparams : (reg, xreg, rflag, cond, asm_op, extra_op, fresh_vars, lowering_options) Arch_params.architecture_params

  val rsp : reg

  val allocatable : reg list
  val xmm_allocatable : xreg list
  val arguments : reg list
  val xmm_arguments : xreg list
  val ret : reg list
  val xmm_ret : xreg list
  val reserved : reg list
  val callee_save : reg list

  val lowering_vars : 'a Conv.coq_tbl -> fresh_vars
  val lowering_opt : lowering_options

  val pp_asm : 'info Conv.coq_tbl -> Format.formatter -> (reg, xreg, rflag, cond, asm_op) Arch_decl.asm_prog -> unit
  val analyze :
    (unit, (reg, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.func ->
    (unit, (reg, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.func ->
    (unit, (reg, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.prog ->
    unit
end

module type Arch = sig
  include Core_arch

  val reg_size : Wsize.wsize
  val rip : var

  val asmOp      : (reg, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.asmOp
  val asmOp_sopn : (reg, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.sopn Sopn.asmOp

  val reg_vars : var list
  val xreg_vars : var list
  val flag_vars : var list
  val argument_vars : var list
  val xmm_argument_vars : var list
  val ret_vars : var list
  val xmm_ret_vars : var list
  val allocatable_vars : var list
  val xmm_allocatable_vars : var list
  val callee_save_vars : var list
  val rsp_var : var
  val all_registers : var list
end

module Arch_from_Core_arch (A : Core_arch) : Arch
