open Utils
open Arch_decl
open Arch_extra
open Prog

type 'a callstyle =
  | StackDirect           (* call instruction push the return address on top of the stack *)
  | ByReg of 'a option    (* call instruction store the return address on a register,
                               (Some r) neams that the register is forced to be r *)

(* TODO: check that we cannot use sth already defined on the Coq side *)

module type Core_arch = sig
  type reg
  type regx
  type xreg
  type rflag
  type cond
  type asm_op
  type extra_op
  type lowering_options

  val asm_e : (reg, regx, xreg, rflag, cond, asm_op, extra_op) asm_extra
  val aparams : (reg, regx, xreg, rflag, cond, asm_op, extra_op, lowering_options) Arch_params.architecture_params
  val call_conv : (reg, regx, xreg, rflag, cond) calling_convention
  val alloc_stack_need_extra : Z.t -> bool

  val lowering_opt : lowering_options
  val not_saved_stack : var list

  val pp_asm : Format.formatter -> (reg, regx, xreg, rflag, cond, asm_op) Arch_decl.asm_prog -> unit

  val callstyle : reg callstyle

  val known_implicits : (Name.t * string) list

  val is_ct_asm_op : asm_op -> bool
  val is_ct_asm_extra : extra_op -> bool

end

module type Arch = sig
  include Core_arch

  val reg_size : Wsize.wsize
  val pointer_data : Wsize.wsize
  val msf_size : Wsize.wsize
  val rip : var

  val asmOp      : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.asmOp
  val asmOp_sopn : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op Sopn.sopn Sopn.asmOp

  val reg_vars  : var list
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

  val arch_info : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Pretyping.arch_info

  val is_ct_sopn : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op -> bool
end

module Arch_from_Core_arch (A : Core_arch) :
  Arch
    with type reg = A.reg
     and type regx = A.regx
     and type xreg = A.xreg
     and type rflag = A.rflag
     and type cond = A.cond
     and type asm_op = A.asm_op
     and type extra_op = A.extra_op = struct
  include A

  let arch_decl = A.asm_e._asm._arch_decl
  let reg_size = arch_decl.reg_size
  let xreg_size = arch_decl.xreg_size
  let pointer_data = arch_pd A.asm_e._asm._arch_decl
  let msf_size = arch_msfsz A.asm_e._asm._arch_decl

  let atoI = A.asm_e._atoI
  (* not sure it is the best place to define [rip], but we need to know [reg_size] *)
  let rip = V.mk "RIP" (Reg (Normal, Direct)) (tu reg_size) L._dummy []

  let asmOp = Arch_extra.asm_opI A.asm_e
  let asmOp_sopn = Sopn.asmOp_sopn pointer_data msf_size asmOp

  let var_of_reg (r:reg) : var = atoI.toI_r.to_ident r

  let reg_vars : var list = List.map var_of_reg arch_decl.toS_r._finC.cenum

  let var_of_regx (r:regx) : var = atoI.toI_rx.to_ident r

  let regx_vars : var list = List.map var_of_regx arch_decl.toS_rx._finC.cenum

  let var_of_xreg (r:xreg) : var = atoI.toI_x.to_ident r

  let xreg_vars : var list = List.map var_of_xreg arch_decl.toS_x._finC.cenum

  let var_of_flag (f:rflag) : var = atoI.toI_f.to_ident f

  let flag_vars : var list = List.map var_of_flag  arch_decl.toS_f._finC.cenum

  let callee_save = call_conv.callee_saved

  (* Remark the order is very important this register allocation use this list to
     allocate register. The lasts in the list are taken only when needed.
     So it is better to have callee_saved at the end *)

  let callee_save_reg  = List.filter_map (Arch_decl.get_ARReg arch_decl) callee_save
  let callee_save_regx = List.filter_map (Arch_decl.get_ARegX arch_decl) callee_save
  let callee_save_xreg = List.filter_map (Arch_decl.get_AXReg arch_decl) callee_save

  let rsp = arch_decl.ad_rsp

  let mk_allocatable regs callee_save =
     List.filter (fun r -> not (List.mem r callee_save)) regs
     @
     callee_save

  let allocatable =
    let good_order = mk_allocatable (Arch_decl.registers arch_decl) callee_save_reg in
    (* be sure that rsp is not used *)
    List.filter (fun r -> r <> rsp) good_order

  let extra_allocatable =
    mk_allocatable (Arch_decl.registerxs arch_decl) callee_save_regx

  let xmm_allocatable =
    mk_allocatable (Arch_decl.xregisters arch_decl) callee_save_xreg

  let arguments = call_conv.call_reg_args

  let xmm_arguments = call_conv.call_xreg_args

  let ret = call_conv.call_reg_ret

  let xmm_ret = call_conv.call_xreg_ret


  let argument_vars =
    List.map var_of_reg arguments

  let xmm_argument_vars =
    List.map var_of_xreg xmm_arguments

  let ret_vars =
    List.map var_of_reg ret

  let xmm_ret_vars =
    List.map var_of_xreg xmm_ret

  let allocatable_vars =
    List.map var_of_reg allocatable

  let extra_allocatable_vars =
    List.map var_of_regx extra_allocatable

  let xmm_allocatable_vars =
    List.map var_of_xreg xmm_allocatable

  let callee_save_vars =
    let var_of_typed = function
      | ARReg r -> var_of_reg  r
      | ARegX r -> var_of_regx r
      | AXReg r -> var_of_xreg r
      | ABReg r -> var_of_flag r in
    List.map var_of_typed callee_save

  let rsp_var = var_of_reg rsp

  let all_registers = reg_vars @ regx_vars @ xreg_vars @ flag_vars

  let syscall_kill = Sv.diff (Sv.of_list all_registers) (Sv.of_list callee_save_vars)

  let callstyle =
    match A.callstyle with
    | StackDirect -> StackDirect
    | ByReg o -> ByReg (Option.map var_of_reg o)

  let arch_info = Pretyping.{
      pd = reg_size;
      asmOp = asmOp_sopn;
      known_implicits = known_implicits;
      flagnames = List.map fst known_implicits;
    }

  let is_ct_sopn (o : (reg, regx, xreg, rflag, cond, asm_op, extra_op) Arch_extra.extended_op) =
   match o with
   | BaseOp (_, o) -> is_ct_asm_op o
   | ExtOp o -> is_ct_asm_extra o

end
