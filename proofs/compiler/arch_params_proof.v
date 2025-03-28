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
  stack_alloc_proof_1
  stack_zeroization_proof
  slh_lowering_proof.
Require Export arch_params.

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

(* Lowering of complex addressing mode for RISC-V.
   It is the identity for the other architectures. *)
Record h_lower_addressing_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra}
  (laparams : lower_addressing_params) :=
  {
    hlap_lower_address_prog_invariants :
      forall fresh_reg p p',
      lap_lower_address laparams fresh_reg p = ok p' ->
      p.(p_globs) = p'.(p_globs) /\ p.(p_extra) = p'.(p_extra);

    hlap_lower_address_fd_invariants :
      forall fresh_reg p p',
      lap_lower_address laparams fresh_reg p = ok p' ->
      forall fn fd,
      get_fundef p.(p_funcs) fn = Some fd ->
      exists2 fd',
        get_fundef p'.(p_funcs) fn = Some fd' &
        [/\ fd.(f_info) = fd'.(f_info),
            fd.(f_tyin) = fd'.(f_tyin),
            fd.(f_params) = fd'.(f_params),
            fd.(f_tyout) = fd'.(f_tyout),
            fd.(f_res) = fd'.(f_res) &
            fd.(f_extra) = fd'.(f_extra)];

    hlap_lower_addressP :
      forall fresh_reg (p p':_sprog),
      lap_lower_address laparams fresh_reg p = ok p' ->
      forall ev scs mem f vs scs' mem' vr,
      sem_call (pT:=progStack) p ev scs mem f vs scs' mem' vr ->
      sem_call (pT:=progStack) p' ev scs mem f vs scs' mem' vr
  }.

Record h_architecture_params
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} {call_conv:calling_convention}
  (lowering_options : Type)
  (aparams : architecture_params lowering_options) :=
  {
    (* Stack alloc hypotheses. See [stack_alloc_proof_1.v]. *)
    hap_hsap :
        stack_alloc_proof_1.h_stack_alloc_params (ap_sap aparams);

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

    (* Lowering of complex addressing mode for RISC-V. Defined above. *)
    hap_hlap : h_lower_addressing_params (ap_lap aparams);

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

