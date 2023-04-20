(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import syscall sem_pexpr_params arch_decl arch_extra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEM_PEXPR_PARAMS.

  Context
    {reg regx xreg rflag cond asm_op extra_op : Type}
    {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
    {syscall_state : Type}
    {scs : syscall_sem syscall_state}.

  #[export]
  Instance spp_of_asm_e : SemPexprParams extended_op syscall_state :=
    {
      _pd := arch_pd;
      _asmop := asm_opI;
      _fcp := ad_fcp;
      _sc_sem := scs;
    }.

End SEM_PEXPR_PARAMS.
