open X86_decl

module X86 (Lowering_params : sig val lowering_vars : 'a Conv.coq_tbl -> X86_lowering.fresh_vars val lowering_opt : X86_lowering.lowering_options end) : Arch_full.Core_arch = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type fresh_vars = X86_lowering.fresh_vars
  type lowering_options = X86_lowering.lowering_options

  let asm_e = X86_extra.x86_extra
  let aparams = X86_params.x86_params
  let call_conv = X86_decl.x86_linux_call_conv

  let rsp = RSP

  let callee_save = call_conv.callee_saved

  (* Remark the order is very important this register allocation use this list to 
     allocate register. The lasts in the list are taken only when needed. 
     So it is better to have callee_saved at the end *)
  let allocatable = 
    let good_order = 
      List.filter (fun r -> not (List.mem r callee_save)) (Arch_decl.registers x86_decl) 
      @
      callee_save in
    (* be sure that rsp is not used *)
    List.filter (fun r -> r <> rsp) good_order  

  let extra_allocatable = Arch_decl.registerxs x86_decl

  let xmm_allocatable = Arch_decl.xregisters x86_decl

  let arguments = call_conv.call_reg_args

  let xmm_arguments = call_conv.call_xreg_args

  let ret = call_conv.call_reg_ret

  let xmm_ret = call_conv.call_xreg_ret

  (* FIXME: this seems to be not used *)
  let reserved = [
    RSP
  ]




  include Lowering_params

  let pp_asm = Ppasm.pp_prog

  let analyze source_f_decl f_decl p =
    let module AbsInt = SafetyInterpreter.AbsAnalyzer(struct
        let main_source = source_f_decl
        let main = f_decl
        let prog = p
      end) in
  (* FIXME: code duplication! already in arch_full.ml *)
  let asmOp = Arch_extra.asm_opI asm_e in
  AbsInt.analyze asmOp ()

end
