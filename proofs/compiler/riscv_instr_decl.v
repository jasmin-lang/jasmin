(* RISC-V 32I instruction set *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  sem_type
  shift_kind
  strings
  utils
  word.
Require xseq.
Require Import
  sopn
  arch_decl
  arch_utils.
Require Import riscv_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module E.
  Definition no_semantics : error := ErrType.
End E.


(* -------------------------------------------------------------------- *)
(* RISC-V 32I instructions (operators). *)

Variant riscv_op : Type :=
(* Arithmetic *)
| ADD                            (* Add without carry *)
.

Scheme Equality for riscv_op.

Lemma riscv_op_eq_axiom : Equality.axiom riscv_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_riscv_op_dec_bl
       internal_riscv_op_dec_lb).
Qed.

#[ export ]
Instance eqTC_riscv_op : eqTypeC riscv_op :=
  { ceqP := riscv_op_eq_axiom }.

Canonical riscv_op_eqType := @ceqT_eqType _ eqTC_riscv_op.

Definition riscv_ops : seq riscv_op :=
  [:: ADD
  ].

Lemma riscv_op_fin_axiom : Finite.axiom riscv_ops.
Proof. by repeat case. Qed.

#[ export ]
Instance finTC_riscv_op : finTypeC riscv_op :=
  {
    cenum := riscv_ops;
    cenumP := riscv_op_fin_axiom;
  }.

Canonical riscv_op_finType := @cfinT_finType _ finTC_riscv_op.

Definition string_of_riscv_op (mn : riscv_op) : string :=
  match mn with
  | ADD => "ADD"
  end%string.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation ty_r := (sem_tuple [:: sreg ]) (only parsing).
Notation ty_rr := (sem_tuple [:: sreg; sreg ]) (only parsing).

(* -------------------------------------------------------------------- *)
(* Printing. *)

Definition pp_riscv_op
  (mn : riscv_op) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_riscv_op mn;
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (reg_size, a)) args;
  |}.


(* -------------------------------------------------------------------- *)
(* Instruction semantics and description. *)
(* All instruction descriptions are made conditional in [riscv_instr_desc] with
   [mk_cond].

   All descriptions have [id_msb_flag] as [MSB_MERGE], but since all
   instructions have a 32-bit output, this is irrelevant. *)

Definition riscv_ADD_semi (wn wm : ty_r) : exec ty_r :=
  let x :=
      (wn + wm)%R
  in
  ok x.

Definition riscv_ADD_instr : instr_desc_t :=
  let mn := ADD in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: E 1; E 2 ];
      id_tout := [:: sreg];
      id_out := [:: E 0 ];
      id_semi := riscv_ADD_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_riscv_op mn);
      id_safe := [::]; (* TODO_RISCV: Complete. *)
      id_pp_asm := pp_riscv_op mn;
    |}.


(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition riscv_instr_desc (mn : riscv_op) : instr_desc_t :=
  match mn with
  | ADD => riscv_ADD_instr
  end.

Definition riscv_prim_string : seq (string * prim_constructor riscv_op) :=
  map (fun mn => (string_of_riscv_op mn, PrimRISCV mn)) cenum.

#[ export ]
Instance riscv_op_decl : asm_op_decl riscv_op :=
  {|
    instr_desc_op := riscv_instr_desc;
    prim_string := riscv_prim_string;
  |}.

Definition riscv_prog := @asm_prog _ _ _ _ _ _ _ riscv_op_decl.
