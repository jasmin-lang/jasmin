(* ARMv8-A (AArch64) instruction set.

   A64 base instructions. Data-processing instructions come in two forms
   selected by the [opts_size] option: the 64-bit (X registers) form and
   the 32-bit (W registers) form, which zeroes the upper 32 bits of
   destination registers. Instruction documentation is quoted from the ARM
   Architecture Reference Manual for A-profile architecture, ARM DDI 0487
   M.a (the machine-readable extraction lives in
   compiler/doc/armv8a_isa_docs.json). *)

From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import ssralg word_ssrZ.

Require Import
  sem_type
  shift_kind
  strings
  utils
  word.
Require xseq.
Require Import
  values
  sopn
  arch_decl
  arch_utils.
Require Import armv8a_decl.


Module E.
  Definition no_semantics : error := ErrSemUndef.
End E.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction options.
   Unlike ARMv7-M, A64 has no conditional execution and flag-setting
   variants are distinct mnemonics (ADDS, SUBS, ...). The options select
   the operand size ([U64] for the X form, [U32] for the W form) and an
   optional shift of the last register operand of data-processing
   instructions. *)

#[only(eqbOK)] derive
Record armv8a_options :=
  {
    has_shift : option shift_kind;
    opts_size : wsize;
  }.

#[ export ]
Instance eqTC_armv8a_options : eqTypeC armv8a_options :=
  { ceqP := armv8a_options_eqb_OK }.

Canonical armv8a_options_eqType := @ceqT_eqType _ eqTC_armv8a_options.

Definition default_opts : armv8a_options :=
  {|
    has_shift := None;
    opts_size := U64;
  |}.

Definition opts_at (ws : wsize) : armv8a_options :=
  {|
    has_shift := None;
    opts_size := ws;
  |}.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction mnemonics. *)

#[only(eqbOK)] derive
Variant armv8a_mnemonic : Type :=
(* Arithmetic *)
| ADD                            (* Add without carry *)
| ADDS                           (* Add without carry, setting flags *)
| ADC                            (* Add with carry *)
| ADCS                           (* Add with carry, setting flags *)
| SUB                            (* Subtract without carry *)
| SUBS                           (* Subtract without carry, setting flags *)
| NEG                            (* Negate *)
| MUL                            (* Multiply and write the least significant
                                    bits of the result *)
| MADD                           (* Multiply and add *)
| MSUB                           (* Multiply and subtract *)
| SDIV                           (* Signed division *)
| UDIV                           (* Unsigned division *)

(* Logical *)
| AND                            (* Bitwise AND *)
| ORR                            (* Bitwise OR *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)

(* Shifts *)
| ASR                            (* Arithmetic shift right *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)

(* Bit field operations *)

(* Other data processing instructions *)
| MOV                            (* Copy operand to destination *)
| MOVN                           (* Move wide with NOT *)
| MOVZ                           (* Move wide with zero *)
| MOVK                           (* Move wide with keep *)
| ADR                            (* Form PC-relative address *)
| SXTB                           (* Sign extend byte *)
| SXTH                           (* Sign extend halfword *)
| SXTW                           (* Sign extend word *)
| UXTB                           (* Zero extend byte *)
| UXTH                           (* Zero extend halfword *)
| UXTW                           (* Zero extend word *)

(* Comparisons *)
| CMP                            (* Compare *)
| TST                            (* Test *)

(* Conditional selection *)
| CSEL                           (* Conditional select *)

(* Loads *)
| LDR                            (* Load a word or doubleword *)
| LDRB                           (* Load a zero extended byte *)
| LDRH                           (* Load a zero extended halfword *)
| LDRSB                          (* Load a sign extended byte *)
| LDRSH                          (* Load a sign extended halfword *)
| LDRSW                          (* Load a sign extended word *)

(* Stores *)
| STR                            (* Store a word or doubleword *)
| STRB                           (* Store a byte *)
| STRH.                          (* Store a halfword *)

#[ export ]
Instance eqTC_armv8a_mnemonic : eqTypeC armv8a_mnemonic :=
  { ceqP := armv8a_mnemonic_eqb_OK }.

Canonical armv8a_mnemonic_eqType := @ceqT_eqType _ eqTC_armv8a_mnemonic.

Definition armv8a_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; AND; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; MOV; MOVN; MOVZ; MOVK; ADR
    ; SXTB; SXTH; SXTW; UXTB; UXTH; UXTW
    ; CMP; TST
    ; CSEL
    ; LDR; LDRB; LDRH; LDRSB; LDRSH; LDRSW
    ; STR; STRB; STRH
  ].

Lemma armv8a_mnemonic_fin_axiom : Finite.axiom armv8a_mnemonics.
Proof. by case. Qed.

#[ export ]
Instance finTC_armv8a_mnemonic : finTypeC armv8a_mnemonic :=
  {
    cenum := armv8a_mnemonics;
    cenumP := armv8a_mnemonic_fin_axiom;
  }.

Canonical armv8a_mnemonic_finType := @cfinT_finType _ finTC_armv8a_mnemonic.

(* Mnemonics whose last register operand can be optionally shifted. *)
Definition has_shift_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; SUB; SUBS; NEG
    ; AND; ORR; EOR; MVN
    ; CMP; TST
  ].

(* The arithmetic instructions (ADD/ADDS/SUB/SUBS/NEG/CMP) only admit
   LSL, LSR and ASR on their shifted-register operand; ROR is reserved
   (C6.2.5 "ADD (shifted register)"). The logical instructions admit all
   four shifts (C6.2.14 "AND (shifted register)"). *)
Definition ror_shift_mnemonics : seq armv8a_mnemonic :=
  [:: AND; ORR; EOR; MVN; TST ].

Definition shift_allowed (mn : armv8a_mnemonic) (sk : shift_kind) : bool :=
  if sk is SROR then mn \in ror_shift_mnemonics else true.

(* Mnemonics available in both the 32-bit (W) and 64-bit (X) forms; the
   remaining mnemonics are only valid with [opts_size = U64]. *)
Definition sized_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; AND; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; MOV; MOVN; MOVZ; MOVK
    ; SXTB; SXTH; UXTB; UXTH
    ; CMP; TST
    ; CSEL
    ; LDR; LDRB; LDRH; LDRSB; LDRSH
    ; STR; STRB; STRH
  ].

Definition wsize_uload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRB); (U16, LDRH); (U32, LDR); (U64, LDR) ].

Definition uload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_uload_mn ws.

Definition wsize_sload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRSB); (U16, LDRSH); (U32, LDRSW) ].

Definition sload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_sload_mn ws.

Definition wsize_of_sload_mn (mn : armv8a_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_sload_mn]) mn.

(* Memory access width of narrow loads; [LDR] accesses at the operand
   size. *)
Definition wsize_of_narrow_load_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | LDRB | LDRSB => Some U8
  | LDRH | LDRSH => Some U16
  | LDRSW => Some U32
  | _ => None
  end.

Definition wsize_store_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, STRB); (U16, STRH); (U32, STR); (U64, STR) ].

Definition store_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_store_mn ws.

Definition wsize_of_narrow_store_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | STRB => Some U8
  | STRH => Some U16
  | _ => None
  end.

Definition string_of_armv8a_mnemonic (mn : armv8a_mnemonic) : string :=
  match mn with
  | ADD => "ADD"
  | ADDS => "ADDS"
  | ADC => "ADC"
  | ADCS => "ADCS"
  | SUB => "SUB"
  | SUBS => "SUBS"
  | NEG => "NEG"
  | MUL => "MUL"
  | MADD => "MADD"
  | MSUB => "MSUB"
  | SDIV => "SDIV"
  | UDIV => "UDIV"
  | AND => "AND"
  | ORR => "ORR"
  | EOR => "EOR"
  | MVN => "MVN"
  | ASR => "ASR"
  | LSL => "LSL"
  | LSR => "LSR"
  | ROR => "ROR"
  | MOV => "MOV"
  | MOVN => "MOVN"
  | MOVZ => "MOVZ"
  | MOVK => "MOVK"
  | ADR => "ADR"
  | SXTB => "SXTB"
  | SXTH => "SXTH"
  | SXTW => "SXTW"
  | UXTB => "UXTB"
  | UXTH => "UXTH"
  | UXTW => "UXTW"
  | CMP => "CMP"
  | TST => "TST"
  | CSEL => "CSEL"
  | LDR => "LDR"
  | LDRB => "LDRB"
  | LDRH => "LDRH"
  | LDRSB => "LDRSB"
  | LDRSH => "LDRSH"
  | LDRSW => "LDRSW"
  | STR => "STR"
  | STRB => "STRB"
  | STRH => "STRH"
  end%string.


(* -------------------------------------------------------------------- *)
(* ARMv8-A operators are pairs of mnemonics and options. *)

#[only(eqbOK)] derive
Variant armv8a_asm_op :=
| ARMv8A_op : armv8a_mnemonic -> armv8a_options -> armv8a_asm_op.

#[ export ]
Instance eqTC_armv8a_asm_op : eqTypeC armv8a_asm_op :=
  { ceqP := armv8a_asm_op_eqb_OK }.

Canonical armv8a_asm_op_eqType := @ceqT_eqType _ eqTC_armv8a_asm_op.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sflag := (lbool) (only parsing).
Notation snzcv := ([:: sflag; sflag; sflag; sflag ]) (only parsing).

Notation ty_nzcv := (sem_ltuple snzcv) (only parsing).
Notation ty_r := (sem_ltuple [:: lreg ]) (only parsing).
Notation ty_w ws := (sem_ltuple [:: lword ws ]) (only parsing).

Notation ty_nzcv_w ws := (sem_ltuple (snzcv ++ [:: lword ws ])) (only parsing).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions. *)

Definition ad_nzcv : seq arg_desc := map F [:: NF; ZF; CF; VF ].


(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (ws : wsize) (w : word ws) := msb w.
Definition ZF_of_word (ws : wsize) (w : word ws) := w == 0%w.

(* Compute the value of the flags for an arithmetic operation.
   For instance, for <+> a binary operation, this function should be called
   with
     res = w <+> w'
     res_unsigned = wunsigned w Z.<+> wunsigned w'
     res_signed = wsigned w Z.<+> wsigned w'
*)
Definition nzcv_of_aluop
  {ws : wsize}
  (res : word ws)     (* Actual result. *)
  (res_unsigned : Z)  (* Result with unsigned interpretation. *)
  (res_signed : Z)    (* Result with signed interpretation. *)
  : ty_nzcv :=
  (:: Some (NF_of_word res)                 (* NF *)
    , Some (ZF_of_word res)                 (* ZF *)
    , Some (wunsigned res != res_unsigned)  (* CF *)
    & Some (wsigned res != res_signed)      (* VF *)
  ).

(* Flags of A64 flag-setting logical instructions (ANDS, BICS, TST):
   PSTATE.<N,Z,C,V> = result<msb>:IsZeroBit(result):'00'. *)
Definition nzcv_of_logop {ws : wsize} (res : word ws) : ty_nzcv :=
  (:: Some (NF_of_word res)
    , Some (ZF_of_word res)
    , Some false
    & Some false
  ).

Definition nzcv_w_of_aluop {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop w wun wsi) (w : ty_w ws).

Definition nzcv_w_of_logop {ws : wsize} (w : word ws) :=
  merge_tuple (nzcv_of_logop w) (w : ty_w ws).


(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Definition mk_semi1_shifted
  {A} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: lword ws ] (exec A)) :
  sem_lprod [:: lword ws; lword8 ] (exec A) :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted
  {A} {o : ltype} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: o; lword ws ] (exec A)) :
  sem_lprod [:: o; lword ws; lword8 ] (exec A) :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

Lemma mk_semi1_shifted_errty A ws sk (semi : sem_lprod [:: lword ws] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: lword ws] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: lword ws] ++ [:: lword8]) (mk_semi1_shifted sk semi).
Proof. by rewrite /mk_semi1_shifted /= => h *; apply h. Qed.

Lemma mk_semi2_2_shifted_errty A (t : ltype) ws sk (semi : sem_lprod [:: t; lword ws] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: t; lword ws] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: t; lword ws] ++ [:: lword8]) (mk_semi2_2_shifted sk semi).
Proof. rewrite /mk_semi2_2_shifted /= => h *; apply h. Qed.

Lemma mk_semi1_shifted_safe A ws sk (semi : sem_lprod [:: lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi1_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma mk_semi2_2_shifted_safe A sk (t : ltype) ws (semi : sem_lprod [:: t; lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi2_2_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma safe_wf_cat (tin tin' : seq ltype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof. apply sub_all => c h; rewrite size_cat; apply: (leq_trans h); apply leq_addr. Qed.

(* On A64 a shifted operand exists only in the register form of an
   instruction (C6.2.5 "ADD (shifted register)" and friends). The immediate
   forms admit either no shift at all (logical instructions, whose bitmask
   immediate is checked by [CAimmC_armv8a_bitmask_imm]) or only
   [LSL #0]/[LSL #12], which is part of the immediate encoding itself and
   folded into [CAimmC_armv8a_arith_imm]. The shifted variant of an
   instruction therefore keeps only the register alternatives of the base
   instruction and appends the shift amount to those. *)
Definition args_kinds_no_imm (x : args_kinds) : bool :=
  ~~ has (has (fun k => if k is CAimm _ _ then true else false)) x.

Definition mk_shifted
  (ws : wsize) (sk : shift_kind) (mn : armv8a_mnemonic)
  (idt : instr_desc_t) semi' semi_errty' semi_safe' : instr_desc_t :=
  {|
    id_msb_flag := idt.(id_msb_flag);
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm (Some (CAimmC_armv8a_shift_amount ws)) U8] ])
        (filter args_kinds_no_imm (id_args_kinds idt));
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_doit := id_doit idt;
    id_pp_asm := id_pp_asm idt;
    (* The descriptor itself rejects a shift kind that the instruction
       does not admit (ROR on the arithmetic class). *)
    id_valid := id_valid idt && shift_allowed mn sk;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_semi_errty := semi_errty';
    id_semi_safe := semi_safe'
  |}.

Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Printing. *)

(* The [wsize] paired with each argument is the width of the register form
   to print: W for widths up to [U32], X for [U64]. It only matters for
   register operands. *)
Definition pp_armv8a_op
  (mn : armv8a_mnemonic) (opts : armv8a_options) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (opts_size opts, a)) args;
  |}.

(* Same as [pp_armv8a_op] with an explicit width per argument, for the
   instructions whose operands are not all [opts_size]-wide (narrow loads
   and stores, 32-bit multiplies, extensions). *)
Definition pp_armv8a_op_szs
  (mn : armv8a_mnemonic) (szs : seq wsize) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := zip szs args;
  |}.


(* -------------------------------------------------------------------- *)
(* Instruction descriptions.
   Descriptions are parameterized by the options: the operand size [osz]
   selects the W or X form (W-form instructions clear the upper 32 bits of
   their destination registers, [MSB_CLEAR]), and data-processing
   instructions gain a shift operand with [mk_shifted] when [has_shift]
   is set.
   Each instruction's semantics ([*_semi], parametric in the operand size
   [ws] unless the instruction exists at a single size) is defined right
   before the description that uses it. *)

Section ARMV8A_INSTR.

Context
  (opts : armv8a_options).

Notation osz := (opts_size opts).

Let string_of_armv8a_mnemonic mn :=
  string_of_armv8a_mnemonic mn.

Notation osz_valid := ((osz == U32) || (osz == U64)) (only parsing).
Notation msbf := (if osz == U64 then MSB_MERGE else MSB_CLEAR) (only parsing).

(* Jasmin-source and EasyCrypt name of the operation: the mnemonics that
   exist in both the W and X forms are size-suffixed (ADD_32 / ADD_64, as
   on x86), matching the intrinsic parser ([armv8a_prim_string] below);
   fixed-size mnemonics keep their bare name. *)
Let armv8a_mn_str (mn : armv8a_mnemonic) : unit -> string :=
  if mn \in sized_mnemonics
  then pp_sz (string_of_armv8a_mnemonic mn) osz
  else pp_s (string_of_armv8a_mnemonic mn).

(* Argument kinds.
   Immediate operands are checked against the A64 encoding rules
   (armv8a_decl.v): [CAimmC_armv8a_arith_imm] (imm12, optionally shifted
   by 12) for the arithmetic class, [CAimmC_armv8a_bitmask_imm] for the
   logical class, [CAimmC_armv8a_mov_imm] for the MOV alias. Instructions
   without an immediate form (BIC, MVN, ...) only accept registers, which
   the [option] parameter of [ak_rr_or_imm]/[ak_rrr_or_imm] expresses
   with [None]. The immediate forms are only available without a shifted
   operand: [mk_shifted] drops them from the shifted variant. *)

Let ak_rr := ak_reg_reg.
Let ak_rrr := ak_reg_reg_reg.
Let ak_rrrr := ak_reg_reg_reg_reg.

Let ak_rr_or_imm (ick : option armv8a_caimm_cond) :=
  if ick is Some ic
  then ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm (Some ic) osz ] ] ]
  else ak_reg_reg.

Let ak_rrr_or_imm (ick : option armv8a_caimm_cond) :=
  if ick is Some ic
  then ak_reg_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some ic) osz ] ] ]
  else ak_reg_reg_reg.

Let ak_rr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ] ] ].

Let ak_r_imm16_shift :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ]; [:: CAimm (Some (CAimmC_armv8a_halfword_shift osz)) U8 ] ] ].

Let ak_rrr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ] ] ].

Let ak_rrr_cond :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAcond ] ] ].

Let ak_r_cond :=
  [:: [:: [:: CAreg ]; [:: CAcond ] ] ].

Let ak_rr_imm8_imm8 :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Let ak_r_imm8_imm8 :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Let ak_rr_imm_imm_extr :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ]; [:: CAimm_sz U8 ] ] ].

(* -------------------------------------------------------------------- *)
(* Arithmetic instructions. *)

(* A binary data-processing instruction without flag outputs, accepting
   an optionally shifted register or an immediate as its last operand. *)
(* [ick] is the immediate-encoding checker for the instruction's immediate
   form ([None] for instructions with no immediate form). *)
Definition mk_arith_instr mn (ick : option armv8a_caimm_cond)
  (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty
                                   (x.(id_semi_errty) (proj1 (andb_prop _ _ h))))
                       (fun h => mk_semi2_2_shifted_safe sk
                                   (x.(id_semi_safe) (proj1 (andb_prop _ _ h))))
  else x.

(* Same as [mk_arith_instr], with the NZCV flags as extra outputs. *)
Definition mk_ariths_instr mn (ick : option armv8a_caimm_cond)
  (semi : word osz -> word osz -> ty_nzcv_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv ++ [:: lword osz ];
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty
                                   (x.(id_semi_errty) (proj1 (andb_prop _ _ h))))
                       (fun h => mk_semi2_2_shifted_safe sk
                                   (x.(id_semi_safe) (proj1 (andb_prop _ _ h))))
  else x.

Notation arith_imm := (Some CAimmC_armv8a_arith_imm) (only parsing).
Notation bitmask_imm := (Some CAimmC_armv8a_bitmask_imm) (only parsing).
Notation no_imm := (None : option armv8a_caimm_cond) (only parsing).

(* [C6.2.6 ADD (shifted register)] ARM DDI 0487 M.a, p. 1798
   Add optionally-shifted register  This instruction adds a register value and
   an optionally-shifted register value, and writes the result to the
   destination register.
   Syntax: ADD <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
*)
Definition armv8a_ADD_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn + wm)%w.

Definition armv8a_ADD_instr : instr_desc_t :=
  mk_arith_instr ADD arith_imm armv8a_ADD_semi.
(* [C6.2.11 ADDS (shifted register)] ARM DDI 0487 M.a, p. 1807
   Add optionally-shifted register, setting flags  This instruction adds a
   register value and an optionally-shifted register value, and writes the
   result to the destination register. It updates the condition flags based on
   the result.  This instruction is used by the alias CMN (shifted register).
   Syntax: ADDS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_ADDS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  nzcv_w_of_aluop
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

Definition armv8a_ADDS_instr : instr_desc_t :=
  mk_ariths_instr ADDS arith_imm armv8a_ADDS_semi.
(* [C6.2.457 SUB (shifted register)] ARM DDI 0487 M.a, p. 2785
   Subtract optionally-shifted register  This instruction subtracts an
   optionally-shifted register value from a register value, and writes the
   result to the destination register.  This instruction is used by the alias
   NEG (shifted register).
   Syntax: SUB <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_SUB_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn - wm)%w.

Definition armv8a_SUB_instr : instr_desc_t :=
  mk_arith_instr SUB arith_imm armv8a_SUB_semi.
(* [C6.2.464 SUBS (shifted register)] ARM DDI 0487 M.a, p. 2797
   Subtract optionally-shifted register, setting flags  This instruction
   subtracts an optionally-shifted register value from a register value, and
   writes the result to the destination register. It updates the condition
   flags based on the result.  This instruction is used by the aliases CMP
   (shifted register) and NEGS.
   Syntax: SUBS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_SUBS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  let wmnot := wnot wm in
  nzcv_w_of_aluop
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

Definition armv8a_SUBS_instr : instr_desc_t :=
  mk_ariths_instr SUBS arith_imm armv8a_SUBS_semi.

(* Add/subtract with carry (no shifted or immediate forms in A64). *)
Definition mk_carry_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition mk_carrys_instr mn (semi : word osz -> word osz -> bool -> ty_nzcv_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := snzcv ++ [:: lword osz ];
    id_out := ad_nzcv ++ [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.2 ADC] ARM DDI 0487 M.a, p. 1789
   Add with carry  This instruction adds two register values and the Carry flag
   value, and writes the result to the destination register.
   Syntax: ADC <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
*)
Definition armv8a_ADC_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_w ws :=
  let c := Z.b2z cf in
  (wn + wm + wrepr ws c)%w.

Definition armv8a_ADC_instr : instr_desc_t := mk_carry_instr ADC armv8a_ADC_semi.
(* [C6.2.3 ADCS] ARM DDI 0487 M.a, p. 1791
   Add with carry, setting flags  This instruction adds two register values and
   the Carry flag value, and writes the result to the destination register. It
   updates the condition flags based on the result.
   Syntax: ADCS <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_ADCS_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_nzcv_w ws :=
  let c := Z.b2z cf in
  nzcv_w_of_aluop
    (wn + wm + wrepr ws c)%w
    (wunsigned wn + wunsigned wm + c)%Z
    (wsigned wn + wsigned wm + c)%Z.

Definition armv8a_ADCS_instr : instr_desc_t := mk_carrys_instr ADCS armv8a_ADCS_semi.
(* [C6.2.294 NEG (shifted register)] ARM DDI 0487 M.a, p. 2440
   Negate (shifted register)  This instruction negates an optionally-shifted
   register value, and writes the result to the destination register.  This is
   an alias of SUB (shifted register). This means:  • The encodings in this
   description are named to match the encodings of SUB (shifted register). •
   The description of SUB (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Note: NEG is an alias of SUB (shifted register) with Rn = ZR; the SUB entry carries the operational pseudocode.
   Syntax: NEG <Xd>, <Xm>{, <shift> #<amount>}  ==  SUB <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUB (shifted register) gives the operational pseudocode for this instruction.
   Base instruction [C6.2.457 SUB (shifted register)] p. 2785, Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_NEG_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  (wnot wm + 1)%w.

Definition armv8a_NEG_instr : instr_desc_t :=
  let mn := NEG in
  let tin := [:: lword osz ] in
  let semi := armv8a_NEG_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi1_shifted sk (id_semi x))
                       (fun h => mk_semi1_shifted_errty
                                   (x.(id_semi_errty) (proj1 (andb_prop _ _ h))))
                       (fun h => mk_semi1_shifted_safe sk
                                   (x.(id_semi_safe) (proj1 (andb_prop _ _ h))))
  else x.

(* A three-register instruction without flags (MUL, SDIV, UDIV, ...). *)
Definition mk_rrr_instr mn (doit_v : doit_t)
  (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.292 MUL] ARM DDI 0487 M.a, p. 2436
   Multiply  This instruction multiplies two register values and writes the
   result to the destination register.  This is an alias of MADD. This means:
   • The encodings in this description are named to match the encodings of
   MADD. • The description of MADD gives the operational pseudocode, any
   CONSTRAINED UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Note: MUL is an alias of MADD with Ra = ZR (see the MADD entry for the operational pseudocode).
   Syntax: MUL <Xd>, <Xn>, <Xm>  ==  MADD <Xd>, <Xn>, <Xm>, XZR
   Operation (ASL):
     The description of MADD gives the operational pseudocode for this instruction.
*)
Definition armv8a_MUL_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn * wm)%w.

Definition armv8a_MUL_instr : instr_desc_t := mk_rrr_instr MUL DOIT armv8a_MUL_semi.
(* [C6.2.356 SDIV] ARM DDI 0487 M.a, p. 2558
   Signed divide  This instruction divides the first signed source register
   value by the second signed source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: SDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = SInt(operand1);
     constant integer divisor = SInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     elsif (dividend < 0) == (divisor < 0) then
         result = Abs(dividend) DIV Abs(divisor); // same signs - positive result
     else
         result = -(Abs(dividend) DIV Abs(divisor)); // different signs - negative result
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_SDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdivi wn wm.

Definition armv8a_SDIV_instr : instr_desc_t :=
  mk_rrr_instr SDIV NOT_DOIT (* Not DIT *) armv8a_SDIV_semi.
(* [C6.2.489 UDIV] ARM DDI 0487 M.a, p. 2846
   Unsigned divide  This instruction divides the first unsigned source register
   value by the second unsigned source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: UDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = UInt(operand1);
     constant integer divisor = UInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     else
         result = dividend DIV divisor;
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_UDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdiv wn wm.

Definition armv8a_UDIV_instr : instr_desc_t :=
  mk_rrr_instr UDIV NOT_DOIT (* Not DIT *) armv8a_UDIV_semi.

(* Multiply-add and multiply-subtract. *)
Definition mk_madd_instr mn (semi : word osz -> word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.274 MADD] ARM DDI 0487 M.a, p. 2401
   Multiply-add  This instruction multiplies two register values, adds a third
   register value, and writes the result to the destination register.  This
   instruction is used by the alias MUL.
   Syntax: MADD <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MADD_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa + wn * wm)%w.

Definition armv8a_MADD_instr : instr_desc_t := mk_madd_instr MADD armv8a_MADD_semi.
(* [C6.2.290 MSUB] ARM DDI 0487 M.a, p. 2432
   Multiply-subtract  This instruction multiplies two register values,
   subtracts the product from a third register value, and writes the result to
   the destination register.  This instruction is used by the alias MNEG.
   Syntax: MSUB <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) - (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MSUB_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa - wn * wm)%w.

Definition armv8a_MSUB_instr : instr_desc_t := mk_madd_instr MSUB armv8a_MSUB_semi.

(* -------------------------------------------------------------------- *)
(* Bitwise instructions. *)

Definition armv8a_bitwise_semi
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : word ws) :
  ty_w ws :=
  op (op0 wn) (op1 wm).

(* [C6.2.15 AND (shifted register)] ARM DDI 0487 M.a, p. 1813
   Bitwise AND (shifted register)  This instruction performs a bitwise AND of a
   register value and an optionally-shifted register value, and writes the
   result to the destination register.
   Syntax: AND <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 AND operand2;
*)
Definition armv8a_AND_instr : instr_desc_t :=
  mk_arith_instr AND bitmask_imm (armv8a_bitwise_semi id id wand).

(* [C6.2.301 ORR (shifted register)] ARM DDI 0487 M.a, p. 2453
   Bitwise OR (shifted register)  This instruction performs a bitwise
   (inclusive) OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.  This instruction is used
   by the alias MOV (register).
   Syntax: ORR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_ORR_instr : instr_desc_t :=
  mk_arith_instr ORR bitmask_imm (armv8a_bitwise_semi id id wor).

(* [C6.2.156 EOR (shifted register)] ARM DDI 0487 M.a, p. 2169
   Bitwise exclusive-OR (shifted register)  This instruction performs a bitwise
   exclusive-OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.
   Syntax: EOR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 EOR operand2;
*)
Definition armv8a_EOR_instr : instr_desc_t :=
  mk_arith_instr EOR bitmask_imm (armv8a_bitwise_semi id id wxor).

(* [C6.2.293 MVN] ARM DDI 0487 M.a, p. 2438
   Bitwise NOT  This instruction writes the bitwise inverse of a register value
   to the destination register.  This is an alias of ORN (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORN (shifted register). • The description of ORN (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MVN <Xd>, <Xm>{, <shift> #<amount>}  ==  ORN <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ORN (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MVN_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  wnot wm.

(* MVN is an alias of ORN (shifted register); it has no immediate form
   (an inverted immediate is a MOV with the complemented value). *)
Definition armv8a_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let tin := [:: lword osz ] in
  let semi := armv8a_MVN_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi1_shifted sk (id_semi x))
                       (fun h => mk_semi1_shifted_errty
                                   (x.(id_semi_errty) (proj1 (andb_prop _ _ h))))
                       (fun h => mk_semi1_shifted_safe sk
                                   (x.(id_semi_safe) (proj1 (andb_prop _ _ h))))
  else x.

(* -------------------------------------------------------------------- *)
(* Shift instructions.
   The shift amount is the value of the second operand modulo the operand
   size; the immediate forms are restricted by the argument checker. Only
   the alias mnemonics (ASR, ...) are provided: they accept registers and
   immediates, subsuming the base variable forms (ASRV, ...), which accept
   only registers and are otherwise identical. *)

(* Shift semantics: the shift amount is the value of the last operand
   modulo the operand size in bits. *)
Definition armv8a_shift_semi
  {ws : wsize} (op : forall sz, word sz -> Z -> word sz)
  (wn : word ws) (wsham : word U8) : ty_w ws :=
  let sham := (wunsigned wsham mod wsize_bits ws)%Z in
  op ws wn sham.

Definition mk_shift_instr mn (op : forall sz, word sz -> Z -> word sz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword U8 ] in
  let semi := armv8a_shift_semi (ws := osz) op in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr ++ ak_rr_imm_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.19 ASR (register)] ARM DDI 0487 M.a, p. 1820
   Arithmetic shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in copies of its sign bit, and
   writes the result to the destination register. The value of the second
   source register modulo the register size in bits gives the number of bits by
   which the first source register is right-shifted.
   Syntax: ASR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ASR_instr : instr_desc_t := mk_shift_instr ASR (@wsar).
(* [C6.2.268 LSL (register)] ARM DDI 0487 M.a, p. 2389
   Logical shift left (register)  This instruction shifts a register value left
   by a variable number of bits, shifting in zeros, and writes the result to
   the destination register. The value of the second source register modulo the
   register size in bits gives the number of bits by which the first source
   register is left-shifted.
   Syntax: LSL <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSL_instr : instr_desc_t := mk_shift_instr LSL (@wshl).
(* [C6.2.271 LSR (register)] ARM DDI 0487 M.a, p. 2395
   Logical shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in zeros, and writes the result
   to the destination register. The value of the second source register modulo
   the register size in bits gives the number of bits by which the first source
   register is right-shifted.
   Syntax: LSR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSR_instr : instr_desc_t := mk_shift_instr LSR (@wshr).
(* [C6.2.347 ROR (register)] ARM DDI 0487 M.a, p. 2541
   Rotate right (register)  This instruction provides the value of the contents
   of a register rotated by a variable number of bits. The bits that are
   rotated off the right end are inserted into the vacated bit positions on the
   left. The value of the second source register modulo the register size in
   bits gives the number of bits by which the first source register is right-
   shifted.
   Syntax: ROR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ROR_instr : instr_desc_t := mk_shift_instr ROR (@wror).

(* -------------------------------------------------------------------- *)
(* Bit field instructions. *)


(* -------------------------------------------------------------------- *)
(* Moves. *)

(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MOV_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  wn.

Definition armv8a_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let tin := [:: lword osz ] in
  let semi := armv8a_MOV_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds :=
      ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm (Some CAimmC_armv8a_mov_imm) osz ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition mk_movw_instr mn (semi : word U16 -> word U8 -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword U16; lword U8 ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.284 MOVZ] ARM DDI 0487 M.a, p. 2418
   Move wide with zero  This instruction moves an optionally-shifted 16-bit
   immediate value to a register.  This instruction is used by the alias MOV
   (wide immediate).
   Syntax: MOVZ <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVZ_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wshl (zero_extend ws imm) (wunsigned wsh).

Definition armv8a_MOVZ_instr : instr_desc_t :=
  mk_movw_instr MOVZ (armv8a_MOVZ_semi (ws := osz)).

(* [C6.2.283 MOVN] ARM DDI 0487 M.a, p. 2416
   Move wide with NOT  This instruction moves the inverse of an optionally-
   shifted 16-bit immediate value to a register.  This instruction is used by
   the alias MOV (inverted wide immediate).
   Syntax: MOVN <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = NOT(result);
*)
Definition armv8a_MOVN_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wnot (wshl (zero_extend ws imm) (wunsigned wsh)).

Definition armv8a_MOVN_instr : instr_desc_t :=
  mk_movw_instr MOVN (armv8a_MOVN_semi (ws := osz)).

(* [C6.2.282 MOVK] ARM DDI 0487 M.a, p. 2415
   Move wide with keep  This instruction moves an optionally-shifted 16-bit
   immediate value into a register, keeping other bits unchanged.
   Syntax: MOVK <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = X[d, datasize];
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVK_semi {ws : wsize} (old : word ws) (imm : word U16) (wsh : word U8) : ty_w ws :=
  let sh := wunsigned wsh in
  let mask := wshl (zero_extend ws (wrepr U16 (-1))) sh in
  wor (wshl (zero_extend ws imm) sh) (wand old (wnot mask)).

Definition armv8a_MOVK_instr : instr_desc_t :=
  let mn := MOVK in
  let tin := [:: lword osz; lword U16; lword U8 ] in
  let semi := armv8a_MOVK_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.


(* -------------------------------------------------------------------- *)
(* Extensions.
   [in_ws] is the width of the extracted low bits; the result is extended
   to the operand size. SXTW and UXTW only exist in the X form. *)

Definition armv8a_extend_semi
  {ws : wsize} (sign : bool) (ws' : wsize) (wn : word ws) : word ws' :=
  let f := if sign then sign_extend else zero_extend in
  (f ws' ws wn).

Definition mk_extend_instr mn (in_ws : wsize) (sign : bool) (valid : bool)
  : instr_desc_t :=
  let tin := [:: lword in_ws ] in
  let semi := armv8a_extend_semi (ws := in_ws) sign osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    (* [SXTB <Xd>, <Wn>] / [UXTB <Wd>, <Wn>]: the source is always a W
       register, and so is the destination of the zero-extensions. *)
    id_pp_asm := pp_armv8a_op_szs mn [:: (if sign then osz else U32); U32 ];
    id_valid := valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.12 ADR] ARM DDI 0487 M.a, p. 1809
   Form PC-relative address  This instruction adds an immediate value to the PC
   value to form a PC-relative address, and writes the result to the
   destination register.
   Syntax: ADR <Xd>, <label>
   Operation (ASL):
     X[d, 64] = PC64 + imm;
*)
Definition armv8a_ADR_semi (wn : word U64) : ty_r :=
  wn.

Definition armv8a_ADR_instr : instr_desc_t :=
  let mn := ADR in
  let tin := [:: lreg ] in
  let semi := armv8a_ADR_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ec 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := NOT_DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.471 SXTB] ARM DDI 0487 M.a, p. 2812
   Signed extend byte  This instruction extracts an 8-bit value from a
   register, sign-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of SBFM. This means:  • The
   encodings in this description are named to match the encodings of SBFM. •
   The description of SBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: SXTB <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #7
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTB_instr : instr_desc_t := mk_extend_instr SXTB U8 true osz_valid.
(* [C6.2.472 SXTH] ARM DDI 0487 M.a, p. 2813
   Sign extend halfword  This instruction extracts a 16-bit value, sign-extends
   it to the size of the register, and writes the result to the destination
   register.  This is an alias of SBFM. This means:  • The encodings in this
   description are named to match the encodings of SBFM. • The description of
   SBFM gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: SXTH <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #15
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTH_instr : instr_desc_t := mk_extend_instr SXTH U16 true osz_valid.
(* [C6.2.473 SXTW] ARM DDI 0487 M.a, p. 2814
   Sign extend word  This instruction sign-extends a word to the size of the
   register, and writes the result to the destination register.  This is an
   alias of SBFM. This means:  • The encodings in this description are named to
   match the encodings of SBFM. • The description of SBFM gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: SXTW <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #31
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTW_instr : instr_desc_t := mk_extend_instr SXTW U32 true (osz == U64).
(* [C6.2.499 UXTB] ARM DDI 0487 M.a, p. 2863
   Unsigned extend byte  This instruction extracts an 8-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTB <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #7
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTB_instr : instr_desc_t := mk_extend_instr UXTB U8 false osz_valid.
(* [C6.2.500 UXTH] ARM DDI 0487 M.a, p. 2864
   Unsigned extend halfword  This instruction extracts a 16-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTH <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #15
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTH_instr : instr_desc_t := mk_extend_instr UXTH U16 false osz_valid.
(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Note: The ARM ARM defines no UXTW entry: UXTW #0 is equivalent to a 32-bit register MOV (alias of ORR (shifted register)), whose 32-bit result is zero-extended to 64 bits; the MOV (register) entry is recorded here in its place.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTW_instr : instr_desc_t := mk_extend_instr UXTW U32 false (osz == U64).

(* -------------------------------------------------------------------- *)
(* Bit-manipulation instructions. *)

(* -------------------------------------------------------------------- *)
(* Comparisons. *)

Definition mk_cmp_instr mn (ick : option armv8a_caimm_cond)
  (semi : word osz -> word osz -> ty_nzcv)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty
                                   (x.(id_semi_errty) (proj1 (andb_prop _ _ h))))
                       (fun h => mk_semi2_2_shifted_safe sk
                                   (x.(id_semi_safe) (proj1 (andb_prop _ _ h))))
  else x.

(* [C6.2.97 CMP (shifted register)] ARM DDI 0487 M.a, p. 1953
   Compare (shifted register)  This instruction subtracts an optionally-shifted
   register value from a register value. It updates the condition flags based
   on the result, and discards the result.  This is an alias of SUBS (shifted
   register). This means:  • The encodings in this description are named to
   match the encodings of SUBS (shifted register). • The description of SUBS
   (shifted register) gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: CMP <Wn>, <Wm>{, <shift> #<amount>}  ==  CMP <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUBS (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_CMP_semi {ws : wsize} (wn wm : word ws) : ty_nzcv :=
  let wmnot := wnot wm in
  nzcv_of_aluop
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

Definition armv8a_CMP_instr : instr_desc_t :=
  mk_cmp_instr CMP arith_imm armv8a_CMP_semi.
(* [C6.2.484 TST (shifted register)] ARM DDI 0487 M.a, p. 2837
   Test (shifted register)  This instruction performs a bitwise AND operation
   on a register value and an optionally-shifted register value. It updates the
   condition flags based on the result, and discards the result.  This is an
   alias of ANDS (shifted register). This means:  • The encodings in this
   description are named to match the encodings of ANDS (shifted register). •
   The description of ANDS (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Syntax: TST <Wn>, <Wm>{, <shift> #<amount>}  ==  TST <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ANDS (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_TST_semi {ws : wsize} (wn wm : word ws) : ty_nzcv :=
  nzcv_of_logop (wand wn wm).

Definition armv8a_TST_instr : instr_desc_t :=
  mk_cmp_instr TST bitmask_imm armv8a_TST_semi.

(* -------------------------------------------------------------------- *)
(* Conditional selection.
   The condition is a first-class operand (the [CAcond] argument kind),
   evaluated by [arm_eval_cond] on the NZCV flags and passed to the
   semantics as a boolean. *)

Definition mk_csel_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrr_cond;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.138 CSEL] ARM DDI 0487 M.a, p. 2138
   Conditional select  This instruction writes the value of the first source
   register to the destination register if the condition is TRUE. If the
   condition is FALSE, it writes the value of the second source register to the
   destination register.
   Syntax: CSEL <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize];
     X[d, datasize] = result;
*)
Definition armv8a_CSEL_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else wm.

Definition armv8a_CSEL_instr := mk_csel_instr CSEL (armv8a_CSEL_semi (ws := osz)).

(* -------------------------------------------------------------------- *)
(* Loads and stores.
   The memory access itself is performed by the framework ([eval_asm_arg]
   reads or writes memory for address arguments); the instruction semantics
   only sign- or zero-extends the transferred value. [LDR] and [STR] access
   memory at the operand size; the narrow loads and stores have their
   access width in the mnemonic. *)

(* [C6.2.217 LDR (register)] ARM DDI 0487 M.a, p. 2275
   Load register (register)  This instruction calculates an address from a base
   register value and an offset register value, loads a word from memory, and
   writes it to a register. The offset register value can optionally be shifted
   and extended. For information about addressing modes, see Load/Store
   addressing modes.
   Syntax: LDR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(datasize) data = Mem[address, datasize DIV 8, accdesc];
     X[t, regsize] = ZeroExtend(data, regsize);
*)
Definition armv8a_load_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_load_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) (isSome (wsize_of_sload_mn mn)) osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    (* The transferred register of the zero-extending narrow loads is
       always a W register ([LDRB <Wt>, ...]); the sign-extending loads
       name it at the operand size ([LDRSB <Wt>|<Xt>, ...]). *)
    id_pp_asm :=
      pp_armv8a_op_szs mn
        [:: (match mn with LDRB | LDRH => U32 | _ => osz end); osz ];
    id_valid := osz_valid && (if mn is LDRSW then osz == U64 else true);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.220 LDRB (register)] ARM DDI 0487 M.a, p. 2283
   Load register byte (register)  This instruction calculates an address from a
   base register value and an offset register value, loads a byte from memory,
   zero-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.222 LDRH (register)] ARM DDI 0487 M.a, p. 2288
   Load register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a halfword
   from memory, zero-extends it, and writes it to a register. For information
   about addressing modes, see Load/Store addressing modes.
   Syntax: LDRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.224 LDRSB (register)] ARM DDI 0487 M.a, p. 2293
   Load register signed byte (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a byte from
   memory, sign-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRSB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.226 LDRSH (register)] ARM DDI 0487 M.a, p. 2298
   Load register signed halfword (register)  This instruction calculates an
   address from a base register value and an offset register value, loads a
   halfword from memory, sign-extends it, and writes it to a register. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDRSH <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.229 LDRSW (register)] ARM DDI 0487 M.a, p. 2304
   Load register signed word (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a word from
   memory, sign-extends it to form a 64-bit value, and writes it to a register.
   The offset register value can be shifted left by 0 or 2 bits. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSW <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(32) data = Mem[address, 4, accdesc];
     X[t, 64] = SignExtend(data, 64);
*)

(* [C6.2.415 STR (register)] ARM DDI 0487 M.a, p. 2693
   Store register (register)  This instruction calculates an address from a
   base register value and an offset register value, and stores a 32-bit word
   or a 64-bit doubleword to the calculated address, from a register. For
   information about addressing modes, see Load/Store addressing modes.  The
   instruction uses an offset addressing mode, that calculates the address used
   for the memory access from a base register value and an offset register
   value. The offset can be optionally shifted and extended.
   Syntax: STR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: STR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, datasize DIV 8, accdesc] = X[t, datasize];
*)
Definition armv8a_store_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_store_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) false wacc in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be an [osz] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: lword wacc ];
    id_out := [:: Eu 1 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_doit := DOIT;
    (* The transferred register of the narrow stores is always a W
       register ([STRB <Wt>, ...]). *)
    id_pp_asm :=
      pp_armv8a_op_szs mn
        [:: (match mn with STRB | STRH => U32 | _ => osz end); osz ];
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.417 STRB (register)] ARM DDI 0487 M.a, p. 2699
   Store register byte (register)  This instruction calculates an address from
   a base register value and an offset register value, and stores a byte from a
   32-bit register to the calculated address. For information about addressing
   modes, see Load/Store addressing modes.  The instruction uses an offset
   addressing mode, that calculates the address used for the memory access from
   a base register value and an offset register value. The offset can be
   optionally shifted and extended.
   Syntax: STRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: STRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 1, accdesc] = X[t, 8];
*)

(* [C6.2.419 STRH (register)] ARM DDI 0487 M.a, p. 2704
   Store register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, and stores a
   halfword from a 32-bit register to the calculated address. For information
   about addressing modes, see Load/Store addressing modes.  The instruction
   uses an offset addressing mode, that calculates the address used for the
   memory access from a base register value and an offset register value. The
   offset can be optionally shifted and extended.
   Syntax: STRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 2, accdesc] = X[t, 16];
*)

(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition mn_desc (mn : armv8a_mnemonic) : instr_desc_t :=
  match mn with
  | ADD => armv8a_ADD_instr
  | ADDS => armv8a_ADDS_instr
  | ADC => armv8a_ADC_instr
  | ADCS => armv8a_ADCS_instr
  | SUB => armv8a_SUB_instr
  | SUBS => armv8a_SUBS_instr
  | NEG => armv8a_NEG_instr
  | MUL => armv8a_MUL_instr
  | MADD => armv8a_MADD_instr
  | MSUB => armv8a_MSUB_instr
  | SDIV => armv8a_SDIV_instr
  | UDIV => armv8a_UDIV_instr
  | AND => armv8a_AND_instr
  | ORR => armv8a_ORR_instr
  | EOR => armv8a_EOR_instr
  | MVN => armv8a_MVN_instr
  | ASR => armv8a_ASR_instr
  | LSL => armv8a_LSL_instr
  | LSR => armv8a_LSR_instr
  | ROR => armv8a_ROR_instr
  | MOV => armv8a_MOV_instr
  | MOVN => armv8a_MOVN_instr
  | MOVZ => armv8a_MOVZ_instr
  | MOVK => armv8a_MOVK_instr
  | ADR => armv8a_ADR_instr
  | SXTB => armv8a_SXTB_instr
  | SXTH => armv8a_SXTH_instr
  | SXTW => armv8a_SXTW_instr
  | UXTB => armv8a_UXTB_instr
  | UXTH => armv8a_UXTH_instr
  | UXTW => armv8a_UXTW_instr
  | CMP => armv8a_CMP_instr
  | TST => armv8a_TST_instr
  | CSEL => armv8a_CSEL_instr
  | LDR => armv8a_load_instr LDR
  | LDRB => armv8a_load_instr LDRB
  | LDRH => armv8a_load_instr LDRH
  | LDRSB => armv8a_load_instr LDRSB
  | LDRSH => armv8a_load_instr LDRSH
  | LDRSW => armv8a_load_instr LDRSW
  | STR => armv8a_store_instr STR
  | STRB => armv8a_store_instr STRB
  | STRH => armv8a_store_instr STRH
  end.

End ARMV8A_INSTR.

Definition armv8a_instr_desc (o : armv8a_asm_op) : instr_desc_t :=
  let '(ARMv8A_op mn opts) := o in
  mn_desc opts mn.

(* Size-suffixed intrinsic parsing: [#ADD] is the X (64-bit) form and
   [#ADD_32] the W form. Fixed-size mnemonics take no suffix. *)
Definition armv8a_prim_sized (mn : armv8a_mnemonic) : prim_constructor armv8a_asm_op :=
  PrimX86
    [:: PVp U64; PVp U32 ]
    (fun s =>
       if s is PVp sz
       then Some (ARMv8A_op mn (opts_at sz))
       else None).

Definition armv8a_prim_string : seq (string * prim_constructor armv8a_asm_op) :=
  map
    (fun mn =>
       (string_of_armv8a_mnemonic mn,
        if mn \in sized_mnemonics
        then armv8a_prim_sized mn
        else primM (ARMv8A_op mn default_opts)))
    cenum.

#[ export ]
Instance armv8a_op_decl : asm_op_decl armv8a_asm_op :=
  {|
    instr_desc_op := armv8a_instr_desc;
    prim_string := armv8a_prim_string;
  |}.

Definition armv8a_prog := @asm_prog _ _ _ _ _ _ _ armv8a_op_decl.
