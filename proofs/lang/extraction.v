Require Import var compiler.
Require arm_params.
Require x86_params.

Require ExtrOcamlBasic.
Require ExtrOcamlString.

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
Extract Constant strings.ascii_cmp => "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Extract Constant expr.VarInfo.t => "Location.t".
Extract Constant expr.VarInfo.witness => "Location._dummy".
Extract Constant expr.var_info => "Location.t".
Extract Constant expr.InstrInfo.t => "IInfo.t".
Extract Constant expr.InstrInfo.witness => "IInfo.dummy".
Extract Constant expr.instr_info => "IInfo.t".
Extract Constant expr.fun_info => "FInfo.t".

Cd  "lang/ocaml".

Extraction Blacklist String List Nat Utils Var Array.

Separate Extraction
  utils
  sopn
  expr
  arch_decl
  x86_decl
  x86_sem.x86_prog
  x86_instr_decl
  x86_extra
  x86_params
  arm_decl
  arm_sem.arm_prog
  arm_instr_decl
  arm_extra
  arm_params
  compiler.

Cd  "../..".
