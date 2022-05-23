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
  stack_alloc
  stack_alloc_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Record lowering_params
  `{asmop : asmOp} (fresh_vars lowering_options : Type) :=
  {
    (* Lower an instruction to architecture-specific instructions. *)
    lop_lower_i :
      lowering_options      (* Lowering options depend on the architecture. *)
      -> (instr_info -> warning_msg -> instr_info)
      -> fresh_vars
      -> (var_i -> bool)    (* Whether the variable is in memory. *)
      -> instr              (* Source instruction. *)
      -> cmd;

    (* Whether all fresh vars are different from each other and
     from those in a list of function declarations. *)
    lop_fvars_correct :
      fresh_vars
      -> forall (eft : eqType) (pT : progT eft),
           seq fun_decl
           -> bool;
  }.

Record architecture_params
  `{asm_e : asm_extra}
  (fresh_vars lowering_options : Type) :=
  {
    (* Stack alloc parameters. See stack_alloc.v. *)
    ap_sap : stack_alloc.stack_alloc_params;

    (* Linearization parameters. See linearization.v. *)
    ap_lip : linearization.linearization_params;

    (* Lowering parameters. Defined above. *)
    ap_lop : lowering_params fresh_vars lowering_options;

    (* Assembly generation parameters. See asm_gen.v. *)
    ap_agp : asm_gen_params;

    (* ------------------------------------------------------------------------ *)
    (* Shared across multiple passes. *)

    (* Whether an instruction is a move instruction_proof.
       This considers possible different instructions and argument sizes. *)
    ap_is_move_op : asm_op_t -> bool;
  }.
