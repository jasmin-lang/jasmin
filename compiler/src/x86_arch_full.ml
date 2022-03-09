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

  (* val rip : reg ?? *)
  let rsp = RSP

  let allocatable = [
      RAX; RCX; RDX;
      RSI; RDI;
      R8; R9; R10; R11;
      RBP;
      RBX;
      R12; R13; R14; R15
    ]

  let extra_allocatable = [
      MM0; MM1; MM2; MM3; MM4; MM5; MM6; MM7
    ]

  let xmm_allocatable = [
    XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15
  ]

  let arguments = [
    RDI; RSI; RDX; RCX;
    R8; R9
  ]

  let xmm_arguments = [
    XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7
  ]

  let ret = [
    RAX; RDX
  ]

  let xmm_ret = [
    XMM0; XMM1
  ]

  let reserved = [
    RSP
  ]

  (* rsp does not need to be saved since it is an invariant
     of jasmin program *)
  let callee_save = [
    RBP; RBX; R12; R13; R14; R15
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
