open Arch_decl
open Arch_extra
open Prog

type 'a callstyle =
  | StackDirect           (* call instruction push the return address on top of the stack *)
  | ByReg of 'a option    (* call instruction store the return address on a register, 
                               (Some r) neams that the register is forced to be r *)
(* x86    : StackDirect 
   arm v7 : ByReg (Some ra)
   riscV  : ByReg (can it be StackDirect too ?)
*)

module type Core_arch = sig
  type reg
  type regx 
  type xreg
  type rflag
  type cond
  type asm_op
  type extra_op
  type fresh_vars
  type lowering_options

  val asm_e : (reg, regx, xreg, rflag, cond, asm_op, extra_op) asm_extra
  val aparams : (reg, regx, xreg, rflag, cond, asm_op, extra_op, fresh_vars, lowering_options) Arch_params.architecture_params
  val call_conv : (reg, regx, xreg, rflag, cond) calling_convention

  val lowering_vars : Conv.coq_tbl -> fresh_vars
  val lowering_opt : lowering_options
  val not_saved_stack : Name.t list

  val pp_asm : Conv.coq_tbl -> Format.formatter -> (reg, regx, xreg, rflag, cond, asm_op) Arch_decl.asm_prog -> unit
  val analyze :
    (unit, (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.func ->
    (unit, (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.func ->
    (unit, (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) Prog.prog ->
    unit
  
  val callstyle : reg callstyle

end

module type Arch = sig
  include Core_arch

  val reg_size : Wsize.wsize
  val rip : var

  val asmOp      : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.asmOp
  val asmOp_sopn : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.sopn Sopn.asmOp

  val reg_vars : var list
  val regx_vars : var list
  val xreg_vars : var list
  val flag_vars : var list
  val argument_vars : var list
  val xmm_argument_vars : var list
  val ret_vars : var list
  val xmm_ret_vars : var list
  val allocatable_vars : var list
  val extra_allocatable_vars : var list
  val xmm_allocatable_vars : var list
  val callee_save_vars : var list
  val not_saved_stack : var list
  val rsp_var : var
  val all_registers : var list
  val syscall_kill : Sv.t

  val callstyle : var callstyle 
  
end

module Arch_from_Core_arch (A : Core_arch) : Arch
