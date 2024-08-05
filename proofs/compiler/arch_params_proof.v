From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import
  compiler_util
  expr
  psem.
Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require
  linearization_proof
  lowering
  stack_alloc_proof
  stack_zeroization_proof
  slh_lowering_proof.
Require Export arch_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Record h_lowering_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} 
  (lowering_options : Type)
  (loparams : lowering_params lowering_options) :=
  {
    hlop_lower_callP :
      forall
        (pT : progT)
        (sCP : semCallParams)
        (p : prog)
        (ev : extra_val_t)
        (options : lowering_options)
        (warning : instr_info -> warning_msg -> instr_info)
        (fv : lowering.fresh_vars)
        (_ : lop_fvars_correct loparams fv (p_funcs p))
        (f : funname)
        (scs: syscall_state_t) (mem : low_memory.mem)
        (scs': syscall_state_t) (mem' : low_memory.mem)
        (va vr : seq value),
        sem_call (dc:= direct_c) p ev scs mem f va scs' mem' vr
        -> let lprog :=
             lowering.lower_prog
               (lop_lower_i loparams)
               options
               warning
               fv
               p
           in
           sem_call lprog ev scs mem f va scs' mem' vr;
  }.

Record h_architecture_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} {call_conv:calling_convention}
  (lowering_options : Type)
  (aparams : architecture_params lowering_options) :=
  {
    (* Stack alloc hypotheses. See [stack_alloc_proof.v]. *)
    hap_hsap :
        stack_alloc_proof.h_stack_alloc_params (ap_sap aparams);

    (* Linearization hypotheses. See [linearization_proof.v]. *)
    hap_hlip :
      linearization_proof.h_linearization_params
        (ap_lip aparams);

    (* The scratch registers in linearize_params must be a register.
       Needed for the compiler proof. *)
    ok_lip_tmp :
      exists r : reg_t,
        of_ident (linearization.lip_tmp (ap_lip aparams)) = Some r;

    ok_lip_tmp2 :
      exists r : reg_t,
        of_ident (linearization.lip_tmp2 (ap_lip aparams)) = Some r;

    (* Lowering hypotheses. Defined above. *)
    hap_hlop : h_lowering_params (ap_lop aparams);

    (* Assembly generation hypotheses. See [asm_gen_proof.v]. *)
    hap_hagp : h_asm_gen_params (ap_agp aparams);

    (* Speculative execution lowering hypothesis *)
    hap_hshp : slh_lowering_proof.h_sh_params (ap_shp aparams);

    (* Stack zeroization hypotheses. See [stack_zeroization_proof.v]. *)
    hap_hszp :
      stack_zeroization_proof.h_stack_zeroization_params (ap_szp aparams);

    (* ------------------------------------------------------------------------ *)
    (* Shared across multiple passes. *)

    hap_is_move_opP :
      forall op vx v,
        ap_is_move_op aparams op
        -> exec_sopn (Oasm op) [:: vx ] = ok v
        -> List.Forall2 value_uincl v [:: vx ];
  }.
