open Arch_decl
open X86_decl
open Wsize

module type X86_input = sig

 val call_conv : (register, register_ext, xmm_register, rflag, condt) calling_convention
 val lowering_opt : X86_lowering.lowering_options

end

let atoI decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty t) L._dummy [] in

  match Arch_extra.MkAToIdent.mk decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module X86_core = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type lowering_options = X86_lowering.lowering_options

  let atoI = atoI x86_decl
  let asm_e = X86_extra.x86_extra atoI
  let aparams = X86_params.x86_params atoI

  let not_saved_stack = (X86_params.x86_liparams atoI).lip_not_saved_stack

  let pp_asm = Ppasm.pp_prog
  let callstyle = Arch_full.StackDirect

  let known_implicits = ["OF","_of_"; "CF", "_cf_"; "SF", "_sf_"; "ZF", "_zf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | DIV _ | IDIV _ -> false
    | _ -> true

  let is_doit_asm_op (o : asm_op) =
    match o with
    | ADC _ -> true
    | ADCX _ -> true
    | ADD _ -> true
    | ADOX _ -> true
    | AESDEC -> true
    | AESDECLAST -> true
    | AESENC -> true
    | AESENCLAST -> true
    | AESIMC -> true
    | AESKEYGENASSIST -> true
    | AND _ -> true
    | ANDN _ -> true
    | BLENDV (VE8, _) -> true
    | BLENDV _ -> false (* Not DOIT *)
    | BSWAP _ -> false (* Not DOIT *)
    | BT _ -> true
    | BTR _ -> true
    | BTS _ -> true
    | CLC -> false (* Not DOIT *)
    | CLFLUSH -> false (* Not DOIT *)
    | CMOVcc _ -> true
    | CMP _ -> true
    | CQO _ -> false (* Not DOIT *)
    | DEC _ -> true
    | DIV _ -> false (* Not DOIT *)
    | IDIV _ -> false (* Not DOIT *)
    | IMUL _ -> true
    | IMULr _ -> true
    | IMULri _ -> true
    | INC _ -> true
    | LEA _ -> true
    | LFENCE -> false (* Not DOIT *)
    | LZCNT _ -> false (* Not DOIT *)
    | MFENCE -> false (* Not DOIT *)
    | MOV _ -> true
    | MOVD _ -> true
    | MOVEMASK (VE8, _) -> true
    | MOVEMASK _ -> false (* Not DOIT *)
    | MOVSX _ -> true
    | MOVV _ -> true
    | MOVX _ -> true
    | POR -> true
    | MOVZX _ -> true
    | MUL _ -> true
    | MULX_lo_hi _ -> true
    | NEG _ -> true
    | NOT _ -> true
    | OR _ -> true
    | PCLMULQDQ -> true
    | PDEP _ -> false (* Not DOIT *)
    | PEXT _ -> false (* Not DOIT *)
    | POPCNT _ -> false (* Not DOIT *)
    | PREFETCHT0 -> false (* Not DOIT *)
    | PREFETCHT1 -> false (* Not DOIT *)
    | PREFETCHT2 -> false (* Not DOIT *)
    | PREFETCHNTA -> false (* Not DOIT *)
    | RCL _ -> false (* Not DOIT *)
    | RCR _ -> false (* Not DOIT *)
    | RDTSC _ -> false (* Not DOIT *)
    | RDTSCP _ -> false (* Not DOIT *)
    | ROL _ -> false (* Not DOIT *)
    | RORX _ -> false (* Not DOIT *)
    | ROR _ -> false (* Not DOIT *)
    | SAL _ -> false (* Not DOIT *)
    | SAR _ -> true
    | SARX _ -> false (* Not DOIT *)
    | SBB _ -> true
    | SETcc -> true
    | SFENCE -> false (* Not DOIT *)
    | SHA256MSG1 -> true
    | SHA256MSG2 -> true
    | SHL _ -> true
    | SHLD _ -> false (* Not DOIT *)
    | SHLX _ -> true
    | SHR _ -> true
    | SHRD _ -> false (* Not DOIT *)
    | SHRX _ -> true
    | STC -> false (* Not DOIT *)
    | SUB _ -> true
    | TEST _ -> true
    | TZCNT _ -> false (* Not DOIT *)
    | VAESDEC _ -> true
    | VAESDECLAST _ -> true
    | VAESENC _ -> true
    | VAESENCLAST _ -> true
    | VAESIMC -> true
    | VAESKEYGENASSIST -> true
    | VBROADCASTI128 -> true
    | VEXTRACTI128 -> true
    | VINSERTI128 -> true
    | VMOV _ -> true
    | VMOVDQA _ -> true
    | VMOVDQU _ -> true
    | VMOVHPD -> false (* Not DOIT *)
    | VMOVLPD -> false (* Not DOIT *)
    | VMOVSHDUP _ -> true
    | VMOVSLDUP _ -> true
    | VPABS _ -> true
    | VPACKSS _ -> true
    | VPACKUS _ -> true
    | VPADD _ -> true
    | VPALIGNR _ -> true
    | VPAND _ -> true
    | VPANDN _ -> true
    | VPAVG _ -> true
    | VPBLEND _ -> true
    | VPBLENDVB _ -> true
    | VPBROADCAST _ -> true
    | VPCLMULQDQ _ -> true
    | VPCMPEQ _ -> true
    | VPCMPGT _ -> true
    | VPERM2I128 -> true
    | VPERMD -> true
    | VPERMQ -> true
    | VPEXTR _ -> true
    | VPINSR _ -> true
    | VPMADDUBSW _ -> true
    | VPMADDWD _ -> true
    | VPMAXS (ve, _) -> ve = VE8 || ve = VE16
    | VPMAXU _ -> true
    | VPMINS (ve, _) -> ve = VE8 || ve = VE16
    | VPMINU _ -> true
    | VPMOVMSKB _ -> true
    | VPMOVSX _ -> true
    | VPMOVZX _ -> true
    | VPMUL _ -> true
    | VPMULH _ -> true
    | VPMULHRS _ -> true
    | VPMULHU _ -> true
    | VPMULL _ -> true
    | VPMULU _ -> true
    | VPOR _ -> true
    | VPSHUFB _ -> true
    | VPSHUFD _ -> true
    | VPSHUFHW _ -> true
    | VPSHUFLW _ -> true
    | VPSIGN _ -> true
    | VPSLL _ -> true
    | VPSLLDQ _ -> true
    | VPSLLV _ -> true
    | VPSRA _ -> true
    | VPSRL _ -> true
    | VPSRLDQ _ -> true
    | VPSRLV _ -> true
    | VPSUB _ -> true
    | VPTEST _ -> true
    | VPUNPCKH _ -> true
    | VPUNPCKL _ -> true
    | VPXOR _ -> true
    | VSHUFPS _ -> false (* Not DOIT *)
    | XCHG _ -> false (* Not DOIT *)
    | XOR _ -> true

  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* All of the extra ops compile into DOIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Oset0 _           -> true
    | Oconcat128        -> true
    | Ox86MOVZX32       -> true
    | Ox86MULX _ws      -> true
    | Ox86MULX_hi _     -> true
    | Ox86SLHinit       -> true
    | Ox86SLHupdate     -> true
    | Ox86SLHmove       -> true
    | Ox86SLHprotect _  -> true

end


module X86 (Lowering_params : X86_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = register_ext
     and type xreg = xmm_register
     and type rflag = rflag
     and type cond = condt
     and type asm_op = X86_instr_decl.x86_op
     and type extra_op = X86_extra.x86_extra_op = struct

  include X86_core

  include Lowering_params

end
