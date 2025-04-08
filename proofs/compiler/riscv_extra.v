From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  utils.
Require Export
  arch_decl
  arch_extra
  riscv_params_core.
Require Import
  riscv_decl
  riscv_instr_decl
  riscv.

Local Notation E n := (sopn.ADExplicit n sopn.ACR_any).


Variant riscv_extra_op : Type :=  
  | SWAP of wsize
  | Oriscv_add_large_imm.

Scheme Equality for riscv_extra_op.

Lemma riscv_extra_op_eq_axiom : Equality.axiom riscv_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_riscv_extra_op_dec_bl
       internal_riscv_extra_op_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build riscv_extra_op riscv_extra_op_eq_axiom.

#[ export ]
Instance eqTC_riscv_extra_op : eqTypeC riscv_extra_op :=
  { ceqP := riscv_extra_op_eq_axiom }.

(* [conflicts] ensures that the returned register is distinct from the first
   argument. *)
Definition Oriscv_add_large_imm_instr : instruction_desc :=
  let ty := sword riscv_reg_size in
  let tin := [:: ty; ty] in
  let semi := fun (x y : word riscv_reg_size) => (x + y)%R in
  {| str    := (fun _ => "add_large_imm"%string)
   ; tin    := tin
   ; i_in   := [:: E 1; E 2]
   ; tout   := [:: ty]
   ; i_out  := [:: E 0]
   ; conflicts := [:: (APout 0, APin 0)]
   ; semi   := sem_prod_ok tin semi
   ; semu   := @values.vuincl_app_sopn_v [:: ty; ty] [:: ty] (sem_prod_ok tin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_safe_wf := refl_equal
   ; i_semi_errty :=  fun _ => sem_prod_ok_error (tin:=tin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin:=tin) semi
 |}.

Definition get_instr_desc (o: riscv_extra_op) : instruction_desc :=
  match o with
  | SWAP ws => Oswap_instr (sword ws)
  | Oriscv_add_large_imm => Oriscv_add_large_imm_instr
   end.
  
(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance riscv_extra_op_decl : asmOp riscv_extra_op | 1 :=
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

Definition asm_args_of_opn_args
  : seq RISCVFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).

Definition assemble_extra
           (ii: instr_info)
           (o: riscv_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with   
  | SWAP sz =>
    if (sz == U32)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (E.internal_error ii "bad RISC-V swap : x = w") in
        Let _ := assert (v_var y != v_var x)
          (E.internal_error ii "bad RISC-V swap : y = x") in
        Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
          (E.error ii "RISC-V swap only valid for register of type u32") in

        ok [:: ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, XOR), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (E.error ii "only register is accepted on source and destination of the swap instruction on RISC-V")
      end
    else
      Error (E.error ii "RISC-V swap only valid for register of type u32")
  | Oriscv_add_large_imm =>
    match outx, inx with
    | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fapp1 (Oword_of_int ws) (Fconst imm))] =>
      Let _ := assert (v_var x != v_var y)
         (E.internal_error ii "bad riscv_add_large_imm: invalid register") in
      Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y])
          (E.error ii "riscv_add_large_imm only valid for register of type u32") in
      ok (asm_args_of_opn_args (RISCVFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (E.internal_error ii "bad riscv_add_large_imm: invalid args or dests")
    end   
  end.

#[ export ]
Instance riscv_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt riscv_op riscv_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition riscv_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ riscv_extra.

Definition Oriscv {atoI : arch_toIdent} o : @sopn riscv_extended_op _ := Oasm (BaseOp (None, o)).
