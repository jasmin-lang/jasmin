(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import syscall sem_params arch_decl arch_extra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEM_PARAMS.

  Context
    {reg regx xreg rflag cond asm_op extra_op : Type}
    {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
    {syscall_state : Type}
    {scs : syscall_sem syscall_state}.

  (* In the proofs where we have an architecture instance, we always have a
     syscall semantics. Forcing the dependency on [scs] makes inference more
     convenient. *)
  #[export]
  Instance ep_of_asm_e {_ : syscall_sem syscall_state} :
    EstateParams syscall_state :=
    {
      _pd := arch_pd;
    }.

  #[export]
  Instance spp_of_asm_e : SemPexprParams :=
    {
      _fcp := ad_fcp;
    }.

  #[export]
  Instance sip_of_asm_e : SemInstrParams extended_op syscall_state :=
    {
      _asmop := asm_opI;
      _sc_sem := scs;
    }.

End SEM_PARAMS.
