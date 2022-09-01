Require Import
  flag_combination
  sopn
  syscall
  wsize.


Class SemPexprParams (asm_op syscall_state : Type) :=
  {
    _pd : PointerData;
    _asmop : asmOp asm_op;
    _fcp :> FlagCombinationParams;
    _sc_sem :> syscall_sem syscall_state;
  }.

Section SEM_PEXPR_PARAMS.

Context
  {asm_op syscall_state : Type}
  {spp : SemPexprParams asm_op syscall_state}.

#[ export ]
Instance pd_of_spp : PointerData | 1000 := _pd.

#[ export ]
Instance asmOp_of_spp : asmOp asm_op | 1000 := _asmop.

End SEM_PEXPR_PARAMS.
