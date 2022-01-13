From mathcomp Require Import all_ssreflect all_algebra.
Require Import arch_extra sopn psem compiler.
Require Import arch_params.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_stack_alloc
  arm_linearization
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition arm_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV opts) =>
      if set_flags opts || is_conditional opts || isSome (has_shift opts)
      then false
      else true
  | _ =>
      false
  end.

Require Import stack_alloc arm_stack_alloc.
Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
  |}.

Definition arm_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := fun _ _ _ _ => lower_i;
    lop_fvars_correct := arm_fvars_correct;
  |}.

Require Import compiler_util asm_gen.
Definition assemble_cond ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v =>
      Let r := of_var_e ii (gv v) in
      match r with
      | NF => ok MI_ct
      | ZF => ok EQ_ct
      | CF => ok CS_ct
      | VF => ok VS_ct
      end

  | _ => Error (E.berror ii e "Invalid condition.")
  end.

Require Import asm_gen.
Definition arm_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.

Definition arm_params :
  architecture_params (asm_e := arm_extra) fresh_vars lowering_options :=
  {| ap_is_move_op := arm_is_move_op
   ; ap_sap := arm_saparams
   ; ap_lip := arm_linearization_params
   ; ap_lop := arm_loparams
   ; ap_agp := arm_agparams
  |}.
