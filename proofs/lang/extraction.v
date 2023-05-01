Require jasmin_compiler.
(* Do not “Require” other modules from Jasmin here:
   expand the jasmin_compiler module instead. *)

From Coq Require ExtrOcamlBasic.
From Coq Require ExtrOcamlString.

(* This is a hack to force the extraction to keep the singleton here,
   This need should be removed if we add more constructor to syscall_t *)
Extract Inductive syscall.syscall_t => "BinNums.positive Syscall_t.syscall_t" ["Syscall_t.RandomBytes"].

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Extraction Inline ssrbool.idP.

Extraction Inline utils.assert.
Extraction Inline utils.Result.bind.
Extraction Inline Datatypes.implb.

Extract Constant strings.ascii_beq => "Char.equal".
Extract Constant strings.ascii_cmp =>
  "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Extract Constant expr.VarInfo.t => "Location.t".
Extract Constant expr.VarInfo.witness => "Location._dummy".
Extract Constant expr.var_info => "Location.t".
Extract Constant expr.InstrInfo.t => "IInfo.t".
Extract Constant expr.InstrInfo.witness => "IInfo.dummy".
Extract Constant expr.instr_info => "IInfo.t".
Extract Constant expr.fun_info => "FInfo.t".
Extract Constant waes.MixColumns => "(fun _ -> failwith ""MixColumns is not implemented"")".
Extract Constant waes.InvMixColumns => "(fun _ -> failwith ""InvMixColumns not implemented"")".

(* Extraction for Ident.CoreIdent *)
Extract Constant PrimInt63.int      => "ExtractInt63.t".
Extract Constant PrimInt63.compares => "ExtractInt63.compare".
Extract Constant PrimInt63.eqb      => "ExtractInt63.equal".

(* Extraction for Var.FunName *)
Extract Constant var.FunName.t   => "CoreIdent.funname".
Extract Constant var.funname     => "CoreIdent.funname".
Extract Constant var.FunName.tag => "CoreIdent.funname_tag".




(* Module Cident *)

Extract Constant ident.Cident.t       => "CoreIdent.Cident.t".
Extract Constant ident.Cident.name    => "CoreIdent.Cident.name".
Extract Constant ident.WrapIdent.t    => "CoreIdent.Cident.t".
Extract Constant ident.WrapIdent.name => "CoreIdent.Cident.name".


Extract Constant ident.Cident.tag     => "CoreIdent.Cident.tag".
Extract Constant ident.Cident.id_name => "CoreIdent.Cident.id_name".

Extract Constant ident.Cident.dummy   => "CoreIdent.Cident.dummy".
Extract Constant ident.Cident.p__     => "CoreIdent.Cident.p__".
Extract Constant ident.Cident.len__   => "CoreIdent.Cident.len__".

Extract Constant ident.Cident.X86.RAX => "CoreIdent.Cident.X86.iRAX".
Extract Constant ident.Cident.X86.RCX => "CoreIdent.Cident.X86.iRCX".
Extract Constant ident.Cident.X86.RDX => "CoreIdent.Cident.X86.iRDX".
Extract Constant ident.Cident.X86.RBX => "CoreIdent.Cident.X86.iRBX".
Extract Constant ident.Cident.X86.RSP => "CoreIdent.Cident.X86.iRSP".
Extract Constant ident.Cident.X86.RBP => "CoreIdent.Cident.X86.iRBP".
Extract Constant ident.Cident.X86.RSI => "CoreIdent.Cident.X86.iRSI".
Extract Constant ident.Cident.X86.RDI => "CoreIdent.Cident.X86.iRDI".
Extract Constant ident.Cident.X86.R8  => "CoreIdent.Cident.X86.iR8".
Extract Constant ident.Cident.X86.R9  => "CoreIdent.Cident.X86.iR9".
Extract Constant ident.Cident.X86.R10 => "CoreIdent.Cident.X86.iR10".
Extract Constant ident.Cident.X86.R11 => "CoreIdent.Cident.X86.iR11".
Extract Constant ident.Cident.X86.R12 => "CoreIdent.Cident.X86.iR12".
Extract Constant ident.Cident.X86.R13 => "CoreIdent.Cident.X86.iR13".
Extract Constant ident.Cident.X86.R14 => "CoreIdent.Cident.X86.iR14".
Extract Constant ident.Cident.X86.R15 => "CoreIdent.Cident.X86.iR15".

Extract Constant ident.Cident.X86.MM0 => "CoreIdent.Cident.X86.iMM0".
Extract Constant ident.Cident.X86.MM1 => "CoreIdent.Cident.X86.iMM1".
Extract Constant ident.Cident.X86.MM2 => "CoreIdent.Cident.X86.iMM2".
Extract Constant ident.Cident.X86.MM3 => "CoreIdent.Cident.X86.iMM3".
Extract Constant ident.Cident.X86.MM4 => "CoreIdent.Cident.X86.iMM4".
Extract Constant ident.Cident.X86.MM5 => "CoreIdent.Cident.X86.iMM5".
Extract Constant ident.Cident.X86.MM6 => "CoreIdent.Cident.X86.iMM6".
Extract Constant ident.Cident.X86.MM7 => "CoreIdent.Cident.X86.iMM7".

Extract Constant ident.Cident.X86.XMM0  => "CoreIdent.Cident.X86.iXMM0".
Extract Constant ident.Cident.X86.XMM1  => "CoreIdent.Cident.X86.iXMM1".
Extract Constant ident.Cident.X86.XMM2  => "CoreIdent.Cident.X86.iXMM2".
Extract Constant ident.Cident.X86.XMM3  => "CoreIdent.Cident.X86.iXMM3".
Extract Constant ident.Cident.X86.XMM4  => "CoreIdent.Cident.X86.iXMM4".
Extract Constant ident.Cident.X86.XMM5  => "CoreIdent.Cident.X86.iXMM5".
Extract Constant ident.Cident.X86.XMM6  => "CoreIdent.Cident.X86.iXMM6".
Extract Constant ident.Cident.X86.XMM7  => "CoreIdent.Cident.X86.iXMM7".
Extract Constant ident.Cident.X86.XMM8  => "CoreIdent.Cident.X86.iXMM8".
Extract Constant ident.Cident.X86.XMM9  => "CoreIdent.Cident.X86.iXMM9".
Extract Constant ident.Cident.X86.XMM10 => "CoreIdent.Cident.X86.iXMM10".
Extract Constant ident.Cident.X86.XMM11 => "CoreIdent.Cident.X86.iXMM11".
Extract Constant ident.Cident.X86.XMM12 => "CoreIdent.Cident.X86.iXMM12".
Extract Constant ident.Cident.X86.XMM13 => "CoreIdent.Cident.X86.iXMM13".
Extract Constant ident.Cident.X86.XMM14 => "CoreIdent.Cident.X86.iXMM14".
Extract Constant ident.Cident.X86.XMM15 => "CoreIdent.Cident.X86.iXMM15".

Extract Constant ident.Cident.X86.CF => "CoreIdent.Cident.X86.iCF".
Extract Constant ident.Cident.X86.PF => "CoreIdent.Cident.X86.iPF".
Extract Constant ident.Cident.X86.ZF => "CoreIdent.Cident.X86.iZF".
Extract Constant ident.Cident.X86.SF => "CoreIdent.Cident.X86.iSF".
Extract Constant ident.Cident.X86.OF => "CoreIdent.Cident.X86.iOF".

Extract Constant ident.Cident.ARM.R00 => "CoreIdent.Cident.ARM.iR00".
Extract Constant ident.Cident.ARM.R01 => "CoreIdent.Cident.ARM.iR01".
Extract Constant ident.Cident.ARM.R02 => "CoreIdent.Cident.ARM.iR02".
Extract Constant ident.Cident.ARM.R03 => "CoreIdent.Cident.ARM.iR03".
Extract Constant ident.Cident.ARM.R04 => "CoreIdent.Cident.ARM.iR04".
Extract Constant ident.Cident.ARM.R05 => "CoreIdent.Cident.ARM.iR05".
Extract Constant ident.Cident.ARM.R06 => "CoreIdent.Cident.ARM.iR06".
Extract Constant ident.Cident.ARM.R07 => "CoreIdent.Cident.ARM.iR07".
Extract Constant ident.Cident.ARM.R08 => "CoreIdent.Cident.ARM.iR08".
Extract Constant ident.Cident.ARM.R09 => "CoreIdent.Cident.ARM.iR09".
Extract Constant ident.Cident.ARM.R10 => "CoreIdent.Cident.ARM.iR10".
Extract Constant ident.Cident.ARM.R11 => "CoreIdent.Cident.ARM.iR11".
Extract Constant ident.Cident.ARM.R12 => "CoreIdent.Cident.ARM.iR12".
Extract Constant ident.Cident.ARM.LR  => "CoreIdent.Cident.ARM.iLR".
Extract Constant ident.Cident.ARM.SP  => "CoreIdent.Cident.ARM.iSP".
Extract Constant ident.Cident.ARM.NF  => "CoreIdent.Cident.ARM.iNF".
Extract Constant ident.Cident.ARM.ZF  => "CoreIdent.Cident.ARM.iZF".
Extract Constant ident.Cident.ARM.CF  => "CoreIdent.Cident.ARM.iCF".
Extract Constant ident.Cident.ARM.VF  => "CoreIdent.Cident.ARM.iVF".





Cd  "lang/ocaml".

Extraction Blacklist String List Nat Utils Var Array.

Separate Extraction
  utils
  warray_
  sopn
  expr
  sem
  sem_params_of_arch_extra
  arch_decl
  x86_decl_core
  x86_decl
  x86_instr_decl
  x86_extra
  x86_params
  arm_decl_core
  arm_decl
  arm_instr_decl
  arm_extra
  arm_params
  compiler.

Cd  "../..".
