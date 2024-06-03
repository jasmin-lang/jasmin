From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

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
  riscv_decl
  riscv_instr_decl
  riscv.

Local Notation E n := (sopn.ADExplicit n None).


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant riscv_extra_op : Type :=  
  | SUBI
  | SWAP of wsize.

Scheme Equality for riscv_extra_op.

Lemma riscv_extra_op_eq_axiom : Equality.axiom riscv_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_riscv_extra_op_dec_bl
       internal_riscv_extra_op_dec_lb).
Qed.

Definition riscv_extra_op_eqMixin :=
  Equality.Mixin riscv_extra_op_eq_axiom.
Canonical riscv_extra_op_eqType :=
  Eval hnf in EqType riscv_extra_op riscv_extra_op_eqMixin.

#[ export ]
Instance eqTC_riscv_extra_op : eqTypeC riscv_extra_op :=
  { ceqP := riscv_extra_op_eq_axiom }.


Definition riscv_SUBI_instr : instruction_desc :=
  {|
   str    := pp_s "SUBI";
   tin    := [::sreg; sreg];
   i_in   := [:: E 1; E 2];
   tout   := [:: sreg];
   i_out  := [:: E 0];
   semi   := riscv_sub_semi;
   semu   := @values.vuincl_app_sopn_v [::sreg; sreg] [::sreg] riscv_sub_semi refl_equal;
   i_safe := [::] 
   |}.

Definition get_instr_desc (o: riscv_extra_op) : instruction_desc :=
  match o with
  | SUBI => riscv_SUBI_instr  
  | SWAP ws => Oswap_instr (sword ws)
   end.
  
(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance riscv_extra_op_decl : asmOp riscv_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::]; (* SUBI should not be used in jazz programm, hence absent from the list *)
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
           (o: riscv_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with 
  | SUBI => 
      match outx, inx with
      | [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fapp1 (Oword_of_int U32) (Fconst imm))] =>
        ok [:: ((None, ADDI), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fapp1 (Oword_of_int U32) (Fconst (- imm)))])]
      | _, _ => Error (E.internal_error ii "ill-formed SUBI : invalid args or dests")
      end
  | SWAP sz =>
    if (sz == U32)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (E.internal_error ii "bad risc-v swap : x = w") in
        Let _ := assert (v_var y != v_var x)
          (E.internal_error ii "bad risc-v swap : y = x") in
        Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
          (E.error ii "risc-v swap only valid for register of type u32") in

        ok [:: ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, XOR), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (E.error ii "only register is accepted on source and destination of the swap instruction on risc-v")
      end
    else
      Error (E.error ii "risc-v swap only valid for register of type u32")
  end.

#[ export ]
Instance riscv_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt riscv_op riscv_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition riscv_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ riscv_extra.

Definition Oriscv {atoI : arch_toIdent} o : @sopn riscv_extended_op _ := Oasm (BaseOp (None, o)).
