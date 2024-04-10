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
(* Printing. *)

Definition pp_name name args :=
  {|
    pp_aop_name := name;
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (reg_size, a)) args;
  |}.

(* RISC-V declares encodings :
  - R type: reg reg -> reg (e.g.: ADD)
  - I type: reg imm -> reg (e.g.: ADDI)
  - S type: reg addr (reg + imm) (e.g.: STORE)
  - B type: reg reg imm (e.g.: BEQ), where imm captures the branch offset), equivalent to S type with imm * 2 (imm[12:1] instead of imm[11:0])
  - U type: imm -> reg (e.g.: LUI)
  - J type: imm -> reg (e.g.: JAL, update PC)
  *)

Definition RTypeInstruction semi jazz_name asm_name: instr_desc_t :=
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := [:: sreg];
      id_out := [:: Ea 0 ];
      id_semi := semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s jazz_name; (* how to print it in Jasmin *)
      id_safe := [::];
      id_pp_asm := pp_name asm_name; (* how to print it in asm *)
    |}.


Definition ITypeInstruction semi jazz_name asm_name: instr_desc_t :=
  {|
      id_msb_flag := MSB_MERGE;
      (* imm are coded on 12 bits, not 32 *)
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := [:: sreg];
      id_out := [:: Ea 0 ];
      id_semi := semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s jazz_name; (* how to print it in Jasmin *)
      id_safe := [::];
      id_pp_asm := pp_name asm_name; (* how to print it in asm *)
    |}.

(* -------------------------------------------------------------------- *)
(* RISC-V 32I instructions (operators). *)

Variant riscv_op : Type :=
(* Arithmetic *)
| ADD                            (* Add register without carry *)
| ADDI                           (* Add immediate without carry *)
| SUB                            (* Sub without carry *)

(* Logical *)
| AND                            (* Bitwise AND with register *)
| ANDI                           (* Bitwise AND with immedate *)
| OR                             (* Bitwise OR with register *)
| ORI                            (* Bitwise OR with immediate *)
| XOR                            (* Bitwise XOR with register *)
| XORI                           (* Bitwise XOR with immediate *)

(* Pseudo instruction : Other data processing instructions *)
| LA                             (* Load address *)
| MV                             (* Copy operand to destination *)
| LI                             (* Load immediate up to 32 bits *)

(* Loads *)
| LOAD of signedness & wsize     (* Load 8 / 16 or 32-bit & signed / unsigned *)

(* Stores *)
| STORE of wsize                 (* Store 8 / 16 or 32-bit values from the low bits of register to memory *)
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


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation ty_r := (sem_tuple [:: sreg ]) (only parsing).
Notation ty_rr := (sem_tuple [:: sreg; sreg ]) (only parsing).

(* -------------------------------------------------------------------- *)
(* Instruction semantics and description. *)

(* TODO: is this comment true? *)
(* All descriptions have [id_msb_flag] as [MSB_MERGE], but since all
   instructions have a 32-bit output, this is irrelevant. *)

Definition riscv_add_semi (wn wm : ty_r) : exec ty_r := ok (wn + wm)%R.

Definition riscv_ADD_instr : instr_desc_t := RTypeInstruction riscv_add_semi "ADD" "add".
Definition prim_ADD := ("ADD"%string, primM ADD).

Definition riscv_ADDI_instr : instr_desc_t := ITypeInstruction riscv_add_semi "ADDI" "addi".
Definition prim_ADDI := ("ADDI"%string, primM ADDI).


Definition riscv_sub_semi (wn wm : ty_r) : exec ty_r := ok (wn - wm)%R.

Definition riscv_SUB_instr : instr_desc_t := RTypeInstruction riscv_sub_semi "SUB" "sub".
Definition prim_SUB := ("SUB"%string, primM SUB).


Definition riscv_and_semi (wn wm : ty_r) : exec ty_r := ok (wand wn wm).

Definition riscv_AND_instr : instr_desc_t := RTypeInstruction riscv_and_semi "AND" "and".
Definition prim_AND := ("AND"%string, primM AND).

Definition riscv_ANDI_instr : instr_desc_t := ITypeInstruction riscv_and_semi "ANDI" "andi".
Definition prim_ANDI := ("ANDI"%string, primM ANDI).


Definition riscv_or_semi (wn wm : ty_r) : exec ty_r := ok (wor wn wm).

Definition riscv_OR_instr : instr_desc_t := RTypeInstruction riscv_or_semi "OR" "or".
Definition prim_OR := ("OR"%string, primM OR).

Definition riscv_ORI_instr : instr_desc_t := ITypeInstruction riscv_or_semi "ORI" "ori".
Definition prim_ORI := ("ORI"%string, primM ORI).


Definition riscv_xor_semi (wn wm : ty_r): exec ty_r := ok (wxor wn wm).

Definition riscv_XOR_instr : instr_desc_t := RTypeInstruction riscv_xor_semi "XOR" "xor".
Definition prim_XOR := ("XOR"%string, primM XOR).

Definition riscv_XORI_instr : instr_desc_t := ITypeInstruction riscv_xor_semi "XORI" "xori".
Definition prim_XORI := ("XORI"%string, primM XORI).


Definition riscv_MV_semi (wn : ty_r) : exec ty_r :=
  ok wn.

Definition riscv_MV_instr : instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg ];
      id_in := [:: Ea 1 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := riscv_MV_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s "MV";
      id_safe := [::];
      id_pp_asm := pp_name "mv";
    |}.

Definition prim_MV := ("MV"%string, primM MV).


Definition riscv_LA_semi (wn : ty_r) : exec ty_r :=
  ok wn.

Definition riscv_LA_instr : instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg ];
      id_in := [:: Ec 1 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := riscv_LA_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_addr;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s "LA";
      id_safe := [::];
      id_pp_asm := pp_name "la";
    |}.

Definition prim_LA := ("LA"%string, primM LA).

Definition riscv_LI_semi (wn : ty_r) : exec ty_r :=
  ok wn.

Definition riscv_LI_instr : instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg ];
      id_in := [:: Ea 1 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := riscv_LI_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s "LI";
      id_safe := [::];
      id_pp_asm := pp_name "li";
    |}.

Definition prim_LI := ("LI"%string, primM LI).


Definition string_of_sign s : string :=
  match s with
  | Signed => ""
  | Unsigned => "u"
  end.

Definition string_of_size ws : string :=
  match ws with
  | U8 => "b"
  | U16 => "h"
  | U32 => "w"
  | _ => "" (* does not apply *)
  end.

Definition pp_sign_sz (s: string) (sign:signedness) (sz : wsize) (_: unit) : string :=
  s ++ "_" ++ (if sign is Signed then "s" else "u")%string ++ string_of_wsize sz.

Definition riscv_extend_semi s ws' ws (w : word ws) : exec (word ws') :=
  let extend := if s is Signed then sign_extend else zero_extend in
  ok (extend ws' ws w).

(* TODO: unaligned access are ok but very discouraged on RISC-V, should we allow them? *)
Definition riscv_LOAD_instr s ws : instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sword ws ];
      id_in := [:: Eu 1 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := @riscv_extend_semi s reg_size ws;
      id_nargs := 2;
      id_args_kinds := ak_reg_addr; (* TODO: are globs allowed? *)
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_sign_sz "LOAD" s ws;
      id_safe := [::];
      id_pp_asm := pp_name ("l" ++ string_of_sign s ++ string_of_size ws);
    |}.

Definition primS (f: signedness -> wsize -> riscv_op) :=
  PrimX86
    [seq PVs sg ws | sg <- [:: Signed; Unsigned], ws <- [:: U8; U16; U32]]
    (fun s => if s is PVs sg ws then (Some (f sg ws)) else None).

Definition prim_LOAD := ("LOAD"%string, primS LOAD).


Definition riscv_STORE_instr ws : instr_desc_t :=
    {|
      id_msb_flag := MSB_MERGE; (* ? *)
      id_tin := [:: sreg ];
      id_in := [:: Ea 0 ];
      id_tout := [:: sword ws ];
      id_out := [:: Eu 1 ];
      id_semi := @riscv_extend_semi Unsigned ws reg_size;
      id_nargs := 2;
      id_args_kinds := ak_reg_addr; (* TODO: are globs allowed? *)
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_sz "STORE" ws;
      id_safe := [::];
      id_pp_asm := pp_name ("s" ++ string_of_size ws);
    |}.

Definition prim_STORE := ("STORE"%string, primP STORE).


(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition riscv_instr_desc (mn : riscv_op) : instr_desc_t :=
  match mn with
  | ADD => riscv_ADD_instr
  | ADDI => riscv_ADDI_instr
  | SUB => riscv_SUB_instr
  | AND => riscv_AND_instr
  | ANDI => riscv_ANDI_instr  
  | OR => riscv_OR_instr
  | ORI => riscv_ORI_instr  
  | XOR => riscv_XOR_instr
  | XORI => riscv_XORI_instr
  | LA => riscv_LA_instr
  | LI => riscv_LI_instr
  | MV => riscv_MV_instr
  | LOAD s ws => riscv_LOAD_instr s ws
  | STORE ws => riscv_STORE_instr ws
  end.

Definition riscv_prim_string : seq (string * prim_constructor riscv_op) := [::
  prim_ADD;
  prim_ADDI;
  prim_SUB;
  prim_OR;
  prim_ORI;
  prim_AND;
  prim_ANDI;
  prim_XOR;
  prim_XORI;
  prim_LA;
  prim_LI;
  prim_MV;
  prim_LOAD;
  prim_STORE
].

#[ export ]
Instance riscv_op_decl : asm_op_decl riscv_op :=
  {|
    instr_desc_op := riscv_instr_desc;
    prim_string := riscv_prim_string;
  |}.

Definition riscv_prog := @asm_prog _ _ _ _ _ _ _ riscv_op_decl.
