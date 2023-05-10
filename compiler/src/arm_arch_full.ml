open Arch_decl
open Prog
open Arm_decl_core
open Arm_decl


module type Arm_input = sig
  val call_conv : (register, Arm_decl.__, Arm_decl.__, rflag, condt) calling_convention

end

module Arm (Lowering_params : Arm_input) : Arch_full.Core_arch = struct
  type reg = register
  type regx = Arm_decl.__
  type xreg = Arm_decl.__
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.__
  type fresh_vars = Arm_lowering.fresh_vars
  type lowering_options = Arm_lowering.lowering_options

  let atoI =
    let open Prog in
    (* FIXME: share the code with x86_arch_full *)
    let mk_var k t s =
      V.mk (Conv.string_of_cstring s) (Reg(k,Direct)) (Conv.ty_of_cty t) L._dummy [] in

    match Arch_extra.MkAToIdent.mk arm_decl mk_var with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
    | Utils0.Ok atoI -> atoI

  let asm_e = Arm_extra.arm_extra atoI
  let aparams = Arm_params.arm_params atoI

  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let lowering_vars =
    let f ty n =
      let v = V.mk n (Reg (Normal, Direct)) ty L._dummy [] in
      Conv.cvar_of_var v
    in
    {
      Arm_lowering.fv_NF = (f tbool "NF").vname;
      Arm_lowering.fv_ZF = (f tbool "ZF").vname;
      Arm_lowering.fv_CF = (f tbool "CF").vname;
      Arm_lowering.fv_VF = (f tbool "VF").vname;
    }

  let lowering_opt = ()

  let not_saved_stack = (Arm_params.arm_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_arm_m4.print_prog

  let callstyle = Arch_full.ByReg (Some LR)
end
