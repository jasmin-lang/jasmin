From mathcomp Require Import all_ssreflect all_algebra.
Require Import arch_extra sopn psem compiler compiler_proof utils.
Require Import arch_params_proof.
Require Import
  arm_decl
  arm_instr_decl
  arm_extra
  arm_linearization_proof
  arm_params
  arm_stack_alloc_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma arm_move_op op :
  ap_is_move_op arm_params op
  -> exists sz,
     let
       opts := {| args_size := sz
               ;  set_flags := false
               ;  is_conditional := false
               ;  has_shift := None
               |}
     in
     op = BaseOp (None, MOV opts).
Proof.
  case: op => [[[|]][]|] // opts.
  case: opts => ? [] [] [] //= _.
  by eexists.
Qed.

Lemma arm_is_move_opP : forall op v vs,
  ap_is_move_op arm_params op ->
  exec_sopn (Oasm op) [:: v ] = ok vs ->
  List.Forall2 value_uincl vs [:: v ].
Proof.
  move=> op v vs H.
  have [sz ->] := (arm_move_op H).
  rewrite /exec_sopn /=.
  t_xrbindP=> w ? Hv.
  elim: (to_wordI Hv) => sz' [w' [le_sz_sz' -> ->]].
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /arm_MOV_semi /=.
  rewrite /check_size_8_32.
  case: (sz <= U32)%CMP => //=.
  move=> [<-] <-.
  constructor; last done.
  exact: (value_uincl_zero_ext w' le_sz_sz').
Qed.

Require Import stack_alloc_proof.
Definition arm_hsaparams : h_stack_alloc_params (ap_sap arm_params).
Proof.
  constructor.
  exact: arm_mov_ofsP.
Defined.

Require Import linearization.
Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R00.
  rewrite /=.
  change "r0"%string with (to_string R00).
  exact: to_stringK.
Qed.

Require Import compiler_util arm_lowering arm_lowering_proof.
Lemma arm_lower_callP
  (eft : eqType)
  (pT : progT eft)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (_ : lop_fvars_correct arm_loparams fv (p_funcs p))
  (f : funname)
  (mem mem' : low_memory.mem)
  (va vr : seq value) :
  psem.sem_call p ev mem f va mem' vr
  -> let lprog :=
       lowering.lower_prog
         (lop_lower_i arm_loparams)
         options
         warning
         fv
         is_var_in_memory
         p
     in
     psem.sem_call lprog ev mem f va mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition arm_hloparams : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.

Definition arm_hyps : h_architecture_params arm_params :=
  {| hap_hsap := arm_hsaparams
   ; hap_hlip := h_arm_linearization_params
   ; ok_lip_tmp := arm_ok_lip_tmp
   ; hap_hlop := arm_hloparams
   ; hap_hagp := TODO_ARM
   ; hap_is_move_opP := arm_is_move_opP
  |}.
