From mathcomp Require Import all_ssreflect all_algebra.
Require Import
  compiler_util
  expr
  psem.
Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen
  asm_gen_proof.
Require
  linearization
  linearization_proof
  lowering
  propagate_inline_proof
  stack_alloc
  stack_alloc_proof.
Require Export arch_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Record h_lowering_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} 
  (fresh_vars lowering_options : Type)
  (loparams : lowering_params fresh_vars lowering_options) :=
  {
    hlop_lower_callP :
      forall
        (eft : eqType)
        (pT : progT eft)
        (sCP : semCallParams)
        (p : prog)
        (ev : extra_val_t)
        (is_regx : var -> bool)
        (options : lowering_options)
        (warning : instr_info -> warning_msg -> instr_info)
        (fv : fresh_vars)
        (is_var_in_memory : var_i -> bool)
        (_ : lop_fvars_correct loparams fv (p_funcs p))
        (f : funname)
        (scs: syscall_state_t) (mem : low_memory.mem)
        (scs': syscall_state_t) (mem' : low_memory.mem)
        (va vr : seq value),
        sem_call p ev scs mem f va scs' mem' vr
        -> let lprog :=
             lowering.lower_prog
               (lop_lower_i loparams is_regx)
               options
               warning
               fv
               is_var_in_memory
               p
           in
           sem_call lprog ev scs mem f va scs' mem' vr;
  }.

Record h_architecture_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} {call_conv:calling_convention}
  (fresh_vars lowering_options : Type)
  (aparams : architecture_params fresh_vars lowering_options) :=
  {
    (* Propagate inline hypotheses. See [propagate_inline_proof.v]. *)
    hap_hpip : propagate_inline_proof.h_propagate_inline_params;

    (* Stack alloc hypotheses. See [stack_alloc_proof.v]. *)
    hap_hsap :
      forall is_regx,
        stack_alloc_proof.h_stack_alloc_params (ap_sap aparams is_regx);

    (* Linearization hypotheses. See [linearization_proof.v]. *)
    hap_hlip :
      linearization_proof.h_linearization_params
        (ap_lip aparams);

    (* The scratch register in linearize_params must be a register.
       Needed for the compiler proof. *)
    ok_lip_tmp :
      exists r : reg_t,
        of_string (linearization.lip_tmp (ap_lip aparams)) = Some r;

    (* Lowering hypotheses. Defined above. *)
    hap_hlop : h_lowering_params (ap_lop aparams);

    (* Assembly generation hypotheses. See [asm_gen_proof.v]. *)
    hap_hagp : h_asm_gen_params (ap_agp aparams);

    (* ------------------------------------------------------------------------ *)
    (* Shared across multiple passes. *)

    hap_is_move_opP :
      forall op vx v,
        ap_is_move_op aparams op
        -> exec_sopn (Oasm op) [:: vx ] = ok v
        -> List.Forall2 value_uincl v [:: vx ];
  }.
