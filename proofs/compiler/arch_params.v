Require Import
  compiler_util
  expr.
Require Import
  arch_decl
  arch_extra.
Require
  linearization
  lowering
  stack_alloc
  stack_zeroization
  slh_lowering
  asm_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Record lowering_params
  `{asmop : asmOp} (lowering_options : Type) :=
  {
    (* Lower an instruction to architecture-specific instructions. *)
    lop_lower_i :
      lowering_options      (* Lowering options depend on the architecture. *)
      -> (instr_info -> warning_msg -> instr_info)
      -> lowering.fresh_vars
      -> instr              (* Source instruction. *)
      -> cmd;

    (* Whether all fresh vars are different from each other and
     from those in a list of function declarations. *)
    lop_fvars_correct :
      lowering.fresh_vars
      -> forall (pT : progT),
           seq fun_decl
           -> bool;
  }.

Record architecture_params
  `{asm_e : asm_extra}
  (lowering_options : Type) :=
  {
    (* Stack alloc parameters. See stack_alloc.v. *)
    ap_sap : stack_alloc.stack_alloc_params;

    (* Linearization parameters. See linearization.v. *)
    ap_lip : linearization.linearization_params;

    (* Lowering parameters. Defined above. *)
    ap_lop : lowering_params lowering_options;

    (* Speculative execution operator lowering parameters. See
       slh_lowering.v. *)
    ap_shp : slh_lowering.sh_params;

    (* Assembly generation parameters. See asm_gen.v. *)
    ap_agp : asm_gen.asm_gen_params;

    (* Stack zeroization parameters. See stack_zeroization.v *)
    ap_szp : stack_zeroization.stack_zeroization_params;

    (* ------------------------------------------------------------------------ *)
    (* Shared across multiple passes. *)

    (* Whether an instruction is a move instruction_proof.
       This considers possible different instructions and argument sizes. *)
    ap_is_move_op : asm_op_t -> bool;
  }.
