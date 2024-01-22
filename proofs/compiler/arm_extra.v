From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  utils.
Require Export
  arch_decl
  arch_extra.
Require Import
  arm_decl
  arm_instr_decl
  arm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant arm_extra_op : Type :=
  | Oarm_swap of wsize.

Scheme Equality for arm_extra_op.

Lemma arm_extra_op_eq_axiom : Equality.axiom arm_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_arm_extra_op_dec_bl
       internal_arm_extra_op_dec_lb).
Qed.

Definition arm_extra_op_eqMixin :=
  Equality.Mixin arm_extra_op_eq_axiom.
Canonical arm_extra_op_eqType :=
  Eval hnf in EqType arm_extra_op arm_extra_op_eqMixin.

#[ export ]
Instance eqTC_arm_extra_op : eqTypeC arm_extra_op :=
  { ceqP := arm_extra_op_eq_axiom }.

(* Extra instructions descriptions. *)
Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  | Oarm_swap sz => Oswap_instr (sword sz) 
  end.

(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance arm_extra_op_decl : asmOp arm_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::];
  }.

Module E.

Definition pass_name := "asmgen"%string.

Definition internal_error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true;
  |}.

Definition error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := false;
  |}.

End E.

Definition assemble_extra
           (ii: instr_info)
           (o: arm_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | Oarm_swap sz => 
     if (sz == U32)%CMP then
       match outx, inx with 
       | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] => 
         (* x, y = swap(z, w) *)
         Let _ := assert (v_var x != v_var w) 
           (E.internal_error ii "bad arm swap : x = w") in
         Let _ := assert (v_var y != v_var x) 
           (E.internal_error ii "bad arm swap : y = x") in
         Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
           (E.error ii "arm swap only valid for register of type u32") in
              
         ok [:: ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);  
                (* x = z ^ w *)
                ((None, ARM_op EOR default_opts), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]); 
                (* y = x ^ w = z ^ w ^ w = z *)
                ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
            ]   (* x = x ^ y = z ^ w ^ z = w *)
       | _, _ => Error (E.error ii "only register is accepted on source and destination of the swap instruction on arm")
       end
     else 
       Error (E.error ii "arm swap only valid for register of type u32")       
  end.

#[ export ]
Instance arm_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ arm_extra.

Definition Oarm {atoI : arch_toIdent} o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
