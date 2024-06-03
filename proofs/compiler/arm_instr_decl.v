(* ARM Cortex-M4 instruction set

   These are the THUMB instructions of ARMv7-M, the instruction set of the M4
   processor. *)

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
  sopn
  arch_decl
  arch_utils.
Require Import arm_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module E.
  Definition no_semantics : error := ErrType.
End E.


(* -------------------------------------------------------------------- *)
(* ARM instruction options. *)

Record arm_options :=
  {
    set_flags : bool;
    is_conditional : bool;
    has_shift : option shift_kind;
  }.

Definition arm_options_beq (ao0 ao1 : arm_options) : bool :=
  [&& set_flags ao0 == set_flags ao1
    , is_conditional ao0 == is_conditional ao1
    & has_shift ao0 == has_shift ao1
  ].

Lemma arm_options_eq_axiom : Equality.axiom arm_options_beq.
Proof.
  move=> [? ? ?] [? ? ?].
  apply: (iffP idP);
    last move=> <-;
    rewrite /arm_options_beq /=.
  - move=> /and3P [].
    repeat move=> /eqP ?.
    by subst.
  - by apply/and3P.
Qed.

#[ export ]
Instance eqTC_arm_options : eqTypeC arm_options :=
  { ceqP := arm_options_eq_axiom }.

Canonical arm_options_eqType := @ceqT_eqType _ eqTC_arm_options.

Lemma arm_options_dec_eq (ao0 ao1 : arm_options) :
  { ao0 = ao1 } + { ao0 <> ao1 }.
Proof.
  case: (ao0 == ao1) /arm_options_eq_axiom.
  - by left.
  - by right.
Qed.

Definition default_opts : arm_options :=
  {|
    set_flags := false;
    is_conditional := false;
    has_shift := None;
  |}.

Definition set_is_conditional (ao : arm_options) : arm_options :=
  {|
    set_flags := set_flags ao;
    is_conditional := true;
    has_shift := has_shift ao;
  |}.

Definition unset_is_conditional (ao : arm_options) : arm_options :=
  {|
    set_flags := set_flags ao;
    is_conditional := false;
    has_shift := has_shift ao;
  |}.


(* -------------------------------------------------------------------- *)
(* ARM instruction mnemonics. *)

Variant halfword : Type :=
| HWB
| HWT
.

Variant arm_mnemonic : Type :=
(* Arithmetic *)
| ADD                            (* Add without carry *)
| ADC                            (* Add with carry *)
| MUL                            (* Multiply and write the least significant
                                    32 bits of the result *)
| MLA                            (* Multiply and accumulate *)
| MLS                            (* Multiply and subtract *)
| SDIV                           (* Signed division *)
| SUB                            (* Subtract without carry *)
| RSB                            (* Reverse subtract without carry *)
| UDIV                           (* Unsigned division *)
| UMULL                          (* Multiply and split the result in two
                                    registers *)
| UMAAL                          (* Multiply and add twice *)
| UMLAL                          (* Multiply and split the result to add it 
                                    to the two destinations*)
| SMULL                          (* Signed version of UMULL*)
| SMLAL                          (* Signed version of UMLAL*)
| SMMUL                          (* Signed multiplication, writes the most significant
                                    32 bits of the result *)
| SMMULR                         (* Rounding version of SMMUL *)

| SMUL_hw of halfword & halfword (* Signed Multiply halfwords. *)
| SMLA_hw of halfword & halfword (* Signed Multiply Accumulate halfwords. *)
| SMULW_hw of halfword           (* Signed Multiply word by halfword. *)

(* Logical *)
| AND                            (* Bitwise AND *)
| BFC                            (* Bit Field Clear *)
| BFI                            (* Bit Field Insert *)
| BIC                            (* Bitwise AND with bitwise NOT *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)
| ORR                            (* Bitwise OR *)

(* Shifts *)
| ASR                            (* Arithmetic shift right *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)
| REV                            (* Byte-Reverse Word reverses the byte order in a 32-bit register. *)
| REV16                          (* Byte-Reverse Packed Halfword reverses the byte order in each 16-bit halfword of a 32-bit register. *)
| REVSH                          (* Byte-Reverse Signed Halfword reverses the byte order in the lower 16-bit halfword of a 32-bit register, and sign extends the result to 32 bits. *)

(* Other data processing instructions *)
| ADR                            (* Adds immediate to PC *)
| MOV                            (* Copy operand to destination *)
| MOVT                           (* Write the top halfword of a register *)
| UBFX                           (* Extract a sub-word and zero extend *)
| UXTB                           (* Extract a byte and zero extend *)
| UXTH                           (* Extract a halfword and zero extend *)
| SBFX                           (* Extract a sub-word and sign extend *)
| CLZ                            (* Count leading zeros. *)

(* Comparison *)
| CMP                            (* Compare *)
| TST                            (* Test *)
| CMN                            (* Compare negative *)

(* Loads *)
| LDR                            (* Load a 32-bit word *)
| LDRB                           (* Load a zero extended byte *)
| LDRH                           (* Load a zero extended halfword *)
| LDRSB                          (* Load a sign extended byte *)
| LDRSH                          (* Load a sign extended halfword *)

(* Stores *)
| STR                            (* Store a 32-bit word *)
| STRB                           (* Store a byte *)
| STRH.                          (* Store a halfword *)

Scheme Equality for arm_mnemonic.

Lemma arm_mnemonic_eq_axiom : Equality.axiom arm_mnemonic_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_arm_mnemonic_dec_bl
       internal_arm_mnemonic_dec_lb).
Qed.

#[ export ]
Instance eqTC_arm_mnemonic : eqTypeC arm_mnemonic :=
  { ceqP := arm_mnemonic_eq_axiom }.

Canonical arm_mnemonic_eqType := @ceqT_eqType _ eqTC_arm_mnemonic.

Definition arm_mnemonics : seq arm_mnemonic :=
  [:: ADD; ADC; MUL; MLA; MLS; SDIV; SUB; RSB; UDIV; UMULL; UMAAL; UMLAL; SMULL; SMLAL; SMMUL; SMMULR
    ; SMUL_hw HWB HWB; SMUL_hw HWB HWT; SMUL_hw HWT HWB; SMUL_hw HWT HWT
    ; SMLA_hw HWB HWB; SMLA_hw HWB HWT; SMLA_hw HWT HWB; SMLA_hw HWT HWT
    ; SMULW_hw HWB; SMULW_hw HWT
    ; AND; BFC; BFI; BIC; EOR; MVN; ORR
    ; ASR; LSL; LSR; ROR; REV; REV16; REVSH
    ; ADR; MOV; MOVT; UBFX; UXTB; UXTH; SBFX; CLZ
    ; CMP; TST; CMN
    ; LDR; LDRB; LDRH; LDRSB; LDRSH
    ; STR; STRB; STRH
  ].

Lemma arm_mnemonic_fin_axiom : Finite.axiom arm_mnemonics.
Proof. by repeat case. Qed.

#[ export ]
Instance finTC_arm_mnemonic : finTypeC arm_mnemonic :=
  {
    cenum := arm_mnemonics;
    cenumP := arm_mnemonic_fin_axiom;
  }.

Canonical arm_mnemonic_finType := @cfinT_finType _ finTC_arm_mnemonic.

Definition set_flags_mnemonics : seq arm_mnemonic :=
  [:: ADD; ADC; MUL; SUB; RSB
    ; AND; BIC; EOR; MVN; ORR
    ; ASR; LSL; LSR; ROR
    ; MOV
  ].

Definition has_shift_mnemonics : seq arm_mnemonic :=
  [:: ADD; ADC; SUB; RSB
    ; AND; BIC; EOR; MVN; ORR
    ; CMP; TST; CMN
  ].

Definition condition_mnemonics : seq arm_mnemonic :=
  [:: CMP; TST ].

Definition always_has_shift_mnemonics : seq (arm_mnemonic * shift_kind) :=
  [:: (UXTB, SROR); (UXTH, SROR) ].

Definition wsize_uload_mn : seq (wsize * arm_mnemonic) :=
  [:: (U8, LDRB); (U16, LDRH); (U32, LDR) ].

Definition uload_mn_of_wsize (ws : wsize) : option arm_mnemonic :=
  xseq.assoc wsize_uload_mn ws.

Definition wsize_of_uload_mn (mn : arm_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_uload_mn]) mn.

Definition wsize_sload_mn : seq (wsize * arm_mnemonic) :=
  [:: (U8, LDRSB); (U16, LDRSH) ].

Definition sload_mn_of_wsize (ws : wsize) : option arm_mnemonic :=
  xseq.assoc wsize_sload_mn ws.

Definition wsize_of_sload_mn (mn : arm_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_sload_mn]) mn.

Definition wsize_of_load_mn (mn : arm_mnemonic) : option wsize :=
  if wsize_of_uload_mn mn is Some ws
  then Some ws
  else wsize_of_sload_mn mn.

Definition wsize_store_mn : seq (wsize * arm_mnemonic) :=
  [:: (U8, STRB); (U16, STRH); (U32, STR) ].

Definition store_mn_of_wsize (ws : wsize) : option arm_mnemonic :=
  xseq.assoc wsize_store_mn ws.

Definition wsize_of_store_mn (mn : arm_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_store_mn]) mn.

Definition string_of_hw (hw : halfword) : string :=
  match hw with
  | HWB => "B"
  | HWT => "T"
  end.

Definition string_of_arm_mnemonic (mn : arm_mnemonic) : string :=
  let with_hw s hw := append s (string_of_hw hw) in
  match mn with
  | ADD => "ADD"
  | ADC => "ADC"
  | MUL => "MUL"
  | MLA => "MLA"
  | MLS => "MLS"
  | SDIV => "SDIV"
  | SUB => "SUB"
  | RSB => "RSB"
  | UDIV => "UDIV"
  | UMULL => "UMULL"
  | UMAAL => "UMAAL"
  | UMLAL => "UMLAL"
  | SMULL => "SMULL"
  | SMLAL => "SMLAL"
  | SMMUL => "SMMUL"
  | SMMULR => "SMMULR"
  | SMUL_hw hw0 hw1 => with_hw (with_hw "SMUL" hw0) hw1
  | SMLA_hw hw0 hw1 => with_hw (with_hw "SMLA" hw0) hw1
  | SMULW_hw hw => with_hw "SMULW" hw
  | AND => "AND"
  | BFC => "BFC"
  | BFI => "BFI"
  | BIC => "BIC"
  | EOR => "EOR"
  | MVN => "MVN"
  | ORR => "ORR"
  | ASR => "ASR"
  | LSL => "LSL"
  | LSR => "LSR"
  | ROR => "ROR"
  | REV => "REV"
  | REV16 => "REV16"
  | REVSH => "REVSH"
  | ADR => "ADR"
  | MOV => "MOV"
  | MOVT => "MOVT"
  | UBFX => "UBFX"
  | UXTB => "UXTB"
  | UXTH => "UXTH"
  | SBFX => "SBFX"
  | CLZ => "CLZ"
  | CMP => "CMP"
  | TST => "TST"
  | LDR => "LDR"
  | LDRB => "LDRB"
  | LDRH => "LDRH"
  | LDRSB => "LDRSB"
  | LDRSH => "LDRSH"
  | STR => "STR"
  | STRB => "STRB"
  | STRH => "STRH"
  | CMN => "CMN"
  end%string.


(* -------------------------------------------------------------------- *)
(* ARM operators are pairs of mnemonics and options. *)

Variant arm_op :=
| ARM_op : arm_mnemonic -> arm_options -> arm_op.

Definition arm_op_beq (op0 op1 : arm_op) : bool :=
  let '(ARM_op mn0 ao0) := op0 in
  let '(ARM_op mn1 ao1) := op1 in
  (mn0 == mn1) && (ao0 == ao1).

Lemma arm_op_eq_axiom : Equality.axiom arm_op_beq.
Proof.
  move=> [mn0 ao0] [mn1 ao1].
  apply: (iffP idP);
    last move=> <-;
    rewrite /arm_op_beq /=.
  - move=> /andP [].
    move=> /arm_mnemonic_eq_axiom <-.
    by move=> /arm_options_eq_axiom <-.
  - apply/andP. split.
    + by apply/arm_mnemonic_eq_axiom.
    + by apply/arm_options_eq_axiom.
Qed.

#[ export ]
Instance eqTC_arm_op : eqTypeC arm_op :=
  { ceqP := arm_op_eq_axiom }.

Canonical arm_op_eqType := @ceqT_eqType _ eqTC_arm_op.

Lemma arm_op_dec_eq (op0 op1 : arm_op) :
  { op0 = op1 } + { op0 <> op1 }.
Proof.
  case: (op0 == op1) /arm_op_eq_axiom.
  - by left.
  - by right.
Qed.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sflag := (sbool) (only parsing).
Notation snz := ([:: sflag; sflag ]) (only parsing).
Notation snzc := ([:: sflag; sflag; sflag ]) (only parsing).
Notation snzcv := ([:: sflag; sflag; sflag; sflag ]) (only parsing).
Notation snz_r := (snz ++ [:: sreg ]) (only parsing).
Notation snzc_r := (snzc ++ [:: sreg ]) (only parsing).
Notation snzcv_r := (snzcv ++ [:: sreg ]) (only parsing).

Notation ty_nzc := (sem_tuple snzc) (only parsing).
Notation ty_nzcv := (sem_tuple snzcv) (only parsing).
Notation ty_r := (sem_tuple [:: sreg ]) (only parsing).
Notation ty_rr := (sem_tuple [:: sreg; sreg ]) (only parsing).
Notation ty_w ws := (sem_tuple [:: sword ws ]) (only parsing).

Notation ty_nz_r := (sem_tuple (snz ++ [:: sreg ])) (only parsing).
Notation ty_nzc_r := (sem_tuple (snzc ++ [:: sreg ])) (only parsing).
Notation ty_nzc_w ws := (sem_tuple (snzc ++ [:: sword ws ])) (only parsing).
Notation ty_nzcv_r := (sem_tuple (snzcv ++ [:: sreg ])) (only parsing).
Notation ty_nzcv_w ws := (sem_tuple (snzcv ++ [:: sword ws ])) (only parsing).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions.*)

Definition ad_nz : seq arg_desc := map F [:: NF; ZF ].
Definition ad_nzc : seq arg_desc := map F [:: NF; ZF; CF ].
Definition ad_nzcv : seq arg_desc := map F [:: NF; ZF; CF; VF ].


(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (ws : wsize) (w : word ws) := msb w.
Definition ZF_of_word (ws : wsize) (w : word ws) := w == 0%R.

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

Definition nzcv_w_of_aluop {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop w wun wsi) (w : ty_w ws).

(* -------------------------------------------------------------------- *)
(* Flag setting transformations.
   Instruction descriptions are defined setting flags. The case where
   the flags should not be set is considered with [drop_nzcv]. *)

Definition drop_nz : instr_desc_t -> instr_desc_t := idt_drop2.
Definition drop_nzc : instr_desc_t -> instr_desc_t := idt_drop3.
Definition drop_nzcv : instr_desc_t -> instr_desc_t := idt_drop4.


(* -------------------------------------------------------------------- *)
(* Conditional transformations.
   Instruction descriptions are defined unconditionally. The following
   transformation converts an unconditional instruction into a conditional
   one.
   The output type is unchanged.
   The input type is expanded with:
   - A boolean. It is used to determine if the instruction is executed
   - The output type. It is used to return the unchanged values if the
     instruction is not exectuted
   The semantics and the rest of the fields are updated accordingly. *)

#[ local ]
Lemma mk_cond_eq_size
  {A B} {x y} {xs0 xs1 : seq A} {ys0 ys1 : seq B} :
  (size xs0 == size ys0) && (size xs1 == size ys1)
  -> (size (xs0 ++ x :: xs1) == size (ys0 ++ y :: ys1))
     && (size xs1 == size ys1).
Proof.
  move=> /andP [] /eqP H0 /eqP H1.
  apply/andP.
  by rewrite 2!size_cat /= H0 H1.
Qed.

#[ local ]
Lemma mk_cond_tin_narr {A} {p : A -> bool} {x} {xs ys : seq A} :
  p x
  -> all p xs
  -> all p ys
  -> all p (xs ++ x :: ys).
Proof.
  move=> Hx Hxs Hys.
  rewrite /= all_cat.
  apply/andP.
  split;
    first done.
  by apply/andP.
Qed.

Definition mk_semi_cond tin tout (semi : sem_prod tin (exec (sem_tuple tout)))
  : sem_prod (tin ++ sbool :: tout) (exec (sem_tuple tout)) :=
  let f0 res cond : sem_prod tout (exec (sem_tuple tout)) :=
    if cond
    then sem_prod_const tout res
    else sem_prod_app (sem_prod_tuple tout) (@Ok _ _)
  in
  let f1 : sem_prod tin (sem_prod (sbool :: tout) (exec (sem_tuple tout))) :=
    sem_prod_app semi f0
  in
  add_arguments f1.

Definition mk_cond (idt : instr_desc_t) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ sbool :: (id_tout idt);
    id_in := (id_in idt) ++ Ea (id_nargs idt) :: (id_out idt);
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := mk_semi_cond (id_semi idt);
    id_nargs := (id_nargs idt).+1;
    id_args_kinds := map (fun x => x ++ [:: [:: CAcond ] ]) (id_args_kinds idt);
    id_eq_size := mk_cond_eq_size (id_eq_size idt);
    id_tin_narr :=
      mk_cond_tin_narr
        (is_true_true: is_not_sarr sbool)
        (id_tin_narr idt)
        (id_tout_narr idt);
    id_tout_narr := id_tout_narr idt;
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_pp_asm := id_pp_asm idt;
  |}.
Arguments mk_cond : clear implicits.


(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Definition mk_semi1_shifted
  {A} (sk : shift_kind) (semi : sem_prod [:: sreg ] (exec A)) :
  sem_prod [:: sreg; sword8 ] (exec A) :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted
  {A} {o : stype} (sk : shift_kind) (semi : sem_prod [:: o; sreg ] (exec A)) :
  sem_prod [:: o; sreg; sword8 ] (exec A) :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

Definition mk_semi3_2_shifted
  {A}
  {o0 o1 : stype}
  (sk : shift_kind)
  (semi : sem_prod [:: o0; sreg; o1 ] (exec A)) :
  sem_prod [:: o0; sreg; o1; sword8 ] (exec A) :=
  fun x wm y shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham) y.

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

#[ local ]
Lemma mk_shifted_tin_narr {A} {p : A -> bool} {x} {xs : seq A} :
  p x
  -> all p xs
  -> all p (xs ++ [:: x ]).
Proof.
  move=> hx hxs.
  rewrite all_cat.
  apply/andP.
  split; first exact: hxs.
  rewrite /= andbT.
  exact: hx.
Qed.

Definition mk_shifted
  (sk : shift_kind) (idt : instr_desc_t) semi' : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: sword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm reg_size] ]) (id_args_kinds idt);
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_tin_narr :=
      mk_shifted_tin_narr
        (is_true_true: is_not_sarr sword8)
        (id_tin_narr idt);
    id_tout_narr := id_tout_narr idt;
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_pp_asm := id_pp_asm idt;
  |}.
Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Printing. *)

Definition pp_arm_op
  (mn : arm_mnemonic) (opts : arm_options) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_arm_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (reg_size, a)) args;
  |}.


(* -------------------------------------------------------------------- *)
(* Instruction semantics and description. *)
(* Data instructions descriptions are defined first as setting flags, and
   without shifts.
   Then, depending on [set_flags], the description is updated with [drop_nzcv].
   After that, depending on [has_shift], shifts are added with [mk_shifted].
   Comparison instructions ignore [has_shift].
   Memory instruction ignore [has_shift] and [set_flags].
   All instruction descriptions are made conditional in [arm_instr_desc] with
   [mk_cond].

   The argument type for shifts is [sword U8] and we must enforce that the
   value is in the appropriate range.
   It can't be [sint] since only words have an interpretation.

   All descriptions have [id_msb_flag] as [MSB_MERGE], but since all
   instructions have a 32-bit output, this is irrelevant. *)

Section ARM_INSTR.

Context
  (opts : arm_options).

Let string_of_arm_mnemonic mn :=
      (string_of_arm_mnemonic mn
        ++ (if set_flags opts then "S" else "")
        ++ (if is_conditional opts then "cc" else ""))%string.

Definition arm_ADD_semi (wn wm : ty_r) : exec ty_nzcv_r :=
  let x :=
    nzcv_w_of_aluop
      (wn + wm)%R
      (wunsigned wn + wunsigned wm)%Z
      (wsigned wn + wsigned wm)%Z
  in
  ok x.

Definition arm_ADD_instr : instr_desc_t :=
  let mn := ADD in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := arm_ADD_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_ADC_semi (wn wm : ty_r) (cf : bool) : exec ty_nzcv_r :=
  let c := Z.b2z cf in
  let x :=
    nzcv_w_of_aluop
      (wn + wm + wrepr reg_size c)%R
      (wunsigned wn + wunsigned wm + c)%Z
      (wsigned wn + wsigned wm + c)%Z
  in
  ok x.

Definition arm_ADC_instr : instr_desc_t :=
  let mn := ADC in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg; sbool ];
      id_in := [:: Ea 1; Ea 2; F CF ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := arm_ADC_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then
      mk_shifted sk x (mk_semi3_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_MUL_semi (wn wm : ty_r) : exec ty_nz_r :=
  let res := (wn * wm)%R in
  ok (:: Some (NF_of_word res), Some (ZF_of_word res) & res).

Definition arm_MUL_instr : instr_desc_t :=
  let mn := MUL in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snz_r;
      id_out := ad_nz ++ [:: Ea 0 ];
      id_semi := arm_MUL_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nz x.

Definition arm_MLA_semi (wn wm wa: ty_r) : exec ty_r :=
  ok (wn * wm + wa)%R.

Definition arm_MLA_instr : instr_desc_t :=
  let mn := MLA in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg; sreg ];
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := arm_MLA_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_MLS_semi (wn wm wa: ty_r) : exec ty_r :=
  ok (wa - wn * wm)%R.

Definition arm_MLS_instr : instr_desc_t :=
  let mn := MLS in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg; sreg ];
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := arm_MLS_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SDIV_semi (wn wm : ty_r) : exec ty_r :=
  ok (wdivi wn wm).

Definition arm_SDIV_instr : instr_desc_t :=
  let mn := SDIV in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_SDIV_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SUB_semi (wn wm : ty_r) : exec ty_nzcv_r :=
  let wmnot := wnot wm in
  let x :=
    nzcv_w_of_aluop
      (wn + wmnot + 1)%R
      (wunsigned wn + wunsigned wmnot + 1)%Z
      (wsigned wn + wsigned wmnot + 1)%Z
  in
  ok x.

Definition arm_SUB_instr : instr_desc_t :=
  let mn := SUB in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := arm_SUB_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_RSB_instr : instr_desc_t :=
  let mn := RSB in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      (* The only difference with SUB is the order of the arguments. *)
      id_semi := fun wn wm => arm_SUB_semi wm wn;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_UDIV_semi (wn wm : ty_r) : exec ty_r :=
  ok (wdiv wn wm).

Definition arm_UDIV_instr : instr_desc_t :=
  let mn := UDIV in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_UDIV_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_UMULL_semi (wn wm : ty_r) : exec ty_rr :=
  ok (wumul wn wm).

Definition arm_UMULL_instr : instr_desc_t :=
  let mn := UMULL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 1; Ea 0 ];
    id_semi := arm_UMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_UMAAL_semi (wa wb wn wm : ty_r) : exec ty_rr :=
  let r := (wunsigned wa + wunsigned wb + wunsigned wn * wunsigned wm)%Z in
  ok (wrepr reg_size r, high_bits reg_size r).

Definition arm_UMAAL_instr : instr_desc_t :=
  let mn := UMAAL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg; sreg; sreg ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := arm_UMAAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_UMLAL_semi (dlo dhi wn wm : ty_r) : exec ty_rr :=
  let (hi, lo) := wumul wn wm in
  ok(wdaddu dhi dlo hi lo).

Definition arm_UMLAL_instr : instr_desc_t :=
  let mn := UMLAL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg; sreg; sreg ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := arm_UMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SMULL_semi (wn wm : ty_r) : exec ty_rr :=
  ok (wsmul wn wm).

Definition arm_SMULL_instr : instr_desc_t :=
  let mn := SMULL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 1; Ea 0 ];
    id_semi := arm_SMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SMLAL_semi (dlo dhi wn wm : ty_r) : exec ty_rr :=
  let (hi, lo) := wsmul wn wm in
  ok(wdadds dhi dlo hi lo).


Definition arm_SMLAL_instr : instr_desc_t :=
  let mn := SMLAL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg; sreg; sreg ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := arm_SMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SMMUL_semi (wn wm : ty_r) : exec ty_r :=
  ok (wmulhs wn wm).

Definition arm_SMMUL_instr : instr_desc_t :=
  let mn := SMMUL in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0];
    id_semi := arm_SMMUL_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.


Definition arm_SMMULR_semi (wn wm : ty_r) : exec ty_r :=
  ok (high_bits reg_size (wsigned wn * wsigned wm + 0x80000000)).

Definition arm_SMMULR_instr : instr_desc_t :=
  let mn := SMMULR in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0];
    id_semi := arm_SMMULR_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition get_hw (hw : halfword) (x : wreg) : u16 :=
  if split_vec 16 x is [:: lo; hi ]
  then if hw is HWT then hi else lo
  else 0%R. (* Never happens. *)

Definition arm_smul_hw_semi (hwn hwm : halfword) (wn wm : wreg) : exec wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m)%Z in
  ok (wrepr U32 r)%R.

Definition arm_smul_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMUL_hw hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_smul_hw_semi hwn hwm;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_smla_hw_semi
  (hwn hwm : halfword) (wn wm acc : wreg) : exec wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m + wsigned acc)%Z in
  ok (wrepr U32 r)%R.

Definition arm_smla_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMLA_hw hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg; sreg ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_smla_hw_semi hwn hwm;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_smulw_hw_semi (hw : halfword) (wn wm : wreg) : exec wreg :=
  let m := get_hw hw wm in
  let res := (wsigned wn * wsigned m)%Z in
  let w := wrepr U64 res in
  ok (winit U32 (fun i => wbit_n w (i + 16))).

Definition arm_smulw_hw_instr hw : instr_desc_t :=
  let mn := SMULW_hw hw in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_smulw_hw_semi hw;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_bitwise_semi
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : ty_w ws) :
  exec (ty_nzc_w ws) :=
  let res := op (op0 wn) (op1 wm) in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , None (* TODO_ARM: Complete. C depends on the shift. *)
       & res
     ).

Definition arm_AND_instr : instr_desc_t :=
  let mn := AND in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_bitwise_semi id id wand;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_BFC_semi (x : wreg) (lsb width : word U8) : exec wreg :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  Let _ := assert (lsbit <? 32)%Z E.no_semantics in
  Let _ := assert (1 <=? nbits)%Z E.no_semantics in
  Let _ := assert (nbits <=? 32 - lsbit)%Z E.no_semantics in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then false
    else wbit_n x i
  in
  ok (winit reg_size mk).

Definition arm_BFC_instr : instr_desc_t :=
  let mn := BFC in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword8; sword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_BFC_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_imm8_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_BFI_semi (x y : wreg) (lsb width : word U8) : exec wreg :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  Let _ := assert (lsbit <? 32)%Z E.no_semantics in
  Let _ := assert (1 <=? nbits)%Z E.no_semantics in
  Let _ := assert (nbits <=? 32 - lsbit)%Z E.no_semantics in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then wbit_n y (i - Z.to_nat lsbit)
    else wbit_n x i
  in
  ok (winit reg_size mk).

Definition arm_BFI_instr : instr_desc_t :=
  let mn := BFI in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sreg; sword8; sword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_BFI_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm8_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_BIC_instr : instr_desc_t :=
  let mn := BIC in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_bitwise_semi id wnot wand;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_EOR_instr : instr_desc_t :=
  let mn := EOR in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_bitwise_semi id id wxor;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_MVN_semi (wn : ty_r) : exec (ty_nzc_r) :=
  let res := wnot wn in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , None (* TODO_ARM: Complete. C depends on the shift. *)
       & res
     ).

Definition arm_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg ];
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_MVN_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi1_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ORR_instr : instr_desc_t :=
  let mn := ORR in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_bitwise_semi id id wor;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ASR_semi (wn : ty_r) (wsham : word U8) : exec ty_nzc_r :=
  (* The bounds for [wsham] are different whether it's an immediate or a
     register: if it's an immediate it must be between 0 and 31, but if it's a
     register it must be between 0 and 255 (the lower byte of the register).
     Since registers only 32 bits it makes no difference. *)
  let sham := wunsigned wsham in
  let res := wsar wn sham in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , Some (msb res)
       & res
     ).

Definition arm_ASR_instr : instr_desc_t :=
  let mn := ASR in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sword U8 ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_ASR_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSL_semi (wn : ty_r) (wsham : word U8) : exec ty_nzc_r :=
  let sham := wunsigned wsham in
  let res := wshl wn sham in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , Some (msb res)
       & res
     ).

Definition arm_LSL_instr : instr_desc_t :=
  let mn := LSL in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sword U8 ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_LSL_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSR_semi (wn : ty_r) (wsham : word U8) : exec ty_nzc_r :=
  let sham := wunsigned wsham in
  let res := wshr wn sham in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , Some (msb res)
       & res
     ).

Definition arm_LSR_instr : instr_desc_t :=
  let mn := LSR in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sword U8 ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_LSR_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ROR_semi (wn : ty_r) (wsham : word U8) : exec ty_nzc_r :=
  let sham := wunsigned wsham in
  let res := wror wn sham in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , Some (msb res)
       & res
     ).

Definition arm_ROR_instr : instr_desc_t :=
  let mn := ROR in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sword U8 ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_ROR_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition mk_rev_instr mn semi :=
  {| id_msb_flag := MSB_MERGE
   ; id_tin := [:: sreg ]
   ; id_in := [:: Ea 1 ]
   ; id_tout := [:: sreg]
   ; id_out := [:: Ea 0 ]
   ; id_semi := semi
   ; id_nargs := 2
   ; id_args_kinds := ak_reg_reg
   ; id_eq_size := refl_equal
   ; id_tin_narr := refl_equal
   ; id_tout_narr := refl_equal
   ; id_check_dest := refl_equal
   ; id_str_jas := pp_s (string_of_arm_mnemonic mn)
   ; id_safe := [::]
   ; id_pp_asm := pp_arm_op mn opts
  |}.

Definition arm_REV_semi (w : ty_r) : exec ty_r :=
  ok (wbswap w).

Definition arm_REV16_semi (w : ty_r) : exec ty_r :=
  ok (lift1_vec U16 (@wbswap U16) U32 w).

Definition arm_REVSH_semi (w : ty_r) : exec ty_r :=
  ok (sign_extend U32 (wbswap (zero_extend U16 w))).

Definition arm_REV_instr   := mk_rev_instr REV   arm_REV_semi.
Definition arm_REV16_instr := mk_rev_instr REV16 arm_REV16_semi.
Definition arm_REVSH_instr := mk_rev_instr REVSH arm_REVSH_semi.

Definition arm_ADR_semi (wn: ty_r) : exec ty_r :=
  ok wn.

Definition arm_ADR_instr : instr_desc_t :=
  let mn := ADR in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg ];
    id_in := [:: Ec 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_ADR_semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_MOV_semi (wn : ty_r) : exec ty_nzc_r :=
  ok (:: Some (NF_of_word wn), Some (ZF_of_word wn), None (* TODO_ARM: Complete *) & wn).

Definition arm_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg ];
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := arm_MOV_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_MOVT_semi (wn : ty_r) (wm : word U16) : exec ty_r :=
  let hi := wshl (zero_extend reg_size wm) 16 in
  let mask := zero_extend reg_size (wrepr U16 (-1)) in
  ok (wor hi (wand wn mask)).

Definition arm_MOVT_instr : instr_desc_t :=
  let mn := MOVT in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U16 ];
    id_in := [:: Ea 0; Ea 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_MOVT_semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: [:: CAreg ]; [:: CAimm U16 ] ] ];
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition bit_field_extract_semi
  (shr : wreg -> Z -> wreg) (wn : wreg) (widx wwidth : word U8) : exec wreg :=
  let idx := wunsigned widx in
  let width := wunsigned wwidth in
  ok (shr (wshl wn (32 - width - idx)%Z) (32 - width)%Z).

Definition arm_UBFX_instr : instr_desc_t :=
  let mn := UBFX in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8; sword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* TODO_ARM: Where to enforce [0 <= widx < 32] and
       [1 <= wwidth < 33-widx]? *)
    id_semi := bit_field_extract_semi (wshr (sz := reg_size));
    id_nargs := 4;
    id_args_kinds :=
      [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm U8 ]; [:: CAimm U8 ] ] ];
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition extend_bits_semi
  (len : Z) (wn : wreg) (wroram : word U8) : exec wreg :=
  let mask := wrepr reg_size (2 ^ len - 1)%Z in
  let roram := wunsigned wroram in
  ok (wand mask (wror wn roram)).

Definition arm_UXTB_instr : instr_desc_t :=
  let mn := UXTB in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8 ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* TODO_ARM: Where to enforce [wroram \in [:: 0; 8; 16; 24 ]]? *)
    id_semi := extend_bits_semi 8;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_UXTH_instr : instr_desc_t :=
  let mn := UXTH in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8 ];
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* TODO_ARM: Where to enforce [wroram \in [:: 0; 8; 16; 24 ]]? *)
    id_semi := extend_bits_semi 16;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm16;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_SBFX_instr : instr_desc_t :=
  let mn := SBFX in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8; sword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* TODO_ARM: Where to enforce [0 <= widx < 32] and
       [1 <= wwidth < 33-widx]? *)
    id_semi := bit_field_extract_semi (wsar (sz := reg_size));
    id_nargs := 4;
    id_args_kinds :=
      [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm U8 ]; [:: CAimm U8 ] ] ];
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_CMP_semi (wn wm : ty_r) : exec ty_nzcv :=
  let wmnot := wnot wm in
  let res :=
    nzcv_of_aluop
      (wn + wmnot + 1)%R
      (wunsigned wn + wunsigned wmnot + 1)%Z
      (wsigned wn + wsigned wmnot + 1)%Z
  in
  ok res.

Definition arm_CMP_instr : instr_desc_t :=
  let mn := CMP in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := arm_CMP_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
  else x.

Definition arm_TST_semi (wn wm : ty_r) : exec ty_nzc :=
  let res := wand wn wm in
  ok
    (:: Some (NF_of_word res)
      , Some (ZF_of_word res)
      & Some false             (* TODO_ARM: C depends on shift or immediate. *)
    ).

Definition arm_TST_instr : instr_desc_t :=
  let mn := TST in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzc;
      id_out := ad_nzc;
      id_semi := arm_TST_semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::]; (* TODO_ARM: Complete. *)
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
  else x.

Definition arm_CMN_instr : instr_desc_t :=
  let mn := CMN in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := fun wn wm => rtuple_drop5th (arm_ADD_semi wn wm);
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
  else x.

Definition arm_extend_semi
  {ws : wsize} (sign : bool) (ws' : wsize) (wn : word ws) : exec (word ws') :=
  let f := if sign then sign_extend else zero_extend in
  ok (f ws' ws wn).

Definition arm_load_instr mn : instr_desc_t :=
  let ws :=
    if wsize_of_load_mn mn is Some ws'
    then ws'
    else U32 (* Never happens. *)
  in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws ];
    id_in := [:: Eu 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := arm_extend_semi (isSome (wsize_of_sload_mn mn)) reg_size;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_store_instr mn : instr_desc_t :=
  let ws :=
    if wsize_of_store_mn mn is Some ws'
    then ws'
    else U32 (* Never happens. *)
  in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be a [reg_size] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := [:: sword ws ];
    id_in := [:: Ea 0 ];
    id_tout := [:: sword ws ];
    id_out := [:: Eu 1 ];
    id_semi := arm_extend_semi false ws;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::]; (* TODO_ARM: Complete. *)
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_CLZ_instr :=
  let mn := CLZ in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg ];
    id_in := [:: Ea 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := fun w => ok (leading_zero w);
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.


(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition mn_desc (mn : arm_mnemonic) : instr_desc_t :=
  match mn with
  | ADD => arm_ADD_instr
  | ADC => arm_ADC_instr
  | MUL => arm_MUL_instr
  | MLA => arm_MLA_instr
  | MLS => arm_MLS_instr
  | SDIV => arm_SDIV_instr
  | SUB => arm_SUB_instr
  | RSB => arm_RSB_instr
  | UDIV => arm_UDIV_instr
  | UMULL => arm_UMULL_instr
  | UMAAL => arm_UMAAL_instr
  | UMLAL => arm_UMLAL_instr
  | SMULL => arm_SMULL_instr
  | SMLAL => arm_SMLAL_instr
  | SMMUL => arm_SMMUL_instr
  | SMMULR => arm_SMMULR_instr
  | SMUL_hw hw0 hw1 => arm_smul_hw_instr hw0 hw1
  | SMLA_hw hw0 hw1 => arm_smla_hw_instr hw0 hw1
  | SMULW_hw hw => arm_smulw_hw_instr hw
  | AND => arm_AND_instr
  | BFC => arm_BFC_instr
  | BFI => arm_BFI_instr
  | BIC => arm_BIC_instr
  | EOR => arm_EOR_instr
  | MVN => arm_MVN_instr
  | ORR => arm_ORR_instr
  | ASR => arm_ASR_instr
  | LSL => arm_LSL_instr
  | LSR => arm_LSR_instr
  | ROR => arm_ROR_instr
  | REV => arm_REV_instr
  | REV16 => arm_REV16_instr
  | REVSH => arm_REVSH_instr
  | ADR => arm_ADR_instr
  | MOV => arm_MOV_instr
  | MOVT => arm_MOVT_instr
  | UBFX => arm_UBFX_instr
  | UXTB => arm_UXTB_instr
  | UXTH => arm_UXTH_instr
  | SBFX => arm_SBFX_instr
  | CLZ => arm_CLZ_instr
  | CMP => arm_CMP_instr
  | TST => arm_TST_instr
  | LDR => arm_load_instr LDR
  | LDRB => arm_load_instr LDRB
  | LDRH => arm_load_instr LDRH
  | LDRSB => arm_load_instr LDRSB
  | LDRSH => arm_load_instr LDRSH
  | STR => arm_store_instr STR
  | STRB => arm_store_instr STRB
  | STRH => arm_store_instr STRH
  | CMN => arm_CMN_instr
  end.

End ARM_INSTR.

Definition arm_instr_desc (o : arm_op) : instr_desc_t :=
  let '(ARM_op mn opts) := o in
  let x := mn_desc opts mn in
  if is_conditional opts
  then mk_cond x
  else x.

Definition arm_prim_string : seq (string * prim_constructor arm_op) :=
  Eval compute in
  let mk_prim mn sf ic :=
    let hs := xseq.assoc always_has_shift_mnemonics mn in
    let opts := {| set_flags := sf; is_conditional := ic; has_shift := hs; |} in
    Let _ :=
      assert
        [|| ~~ sf | mn \in set_flags_mnemonics ]
        "this mnemonic cannot set flags"%string
    in
    ok (ARM_op mn opts)
  in
  map (fun mn => (string_of_arm_mnemonic mn, PrimARM (mk_prim mn))) cenum.

#[ export ]
Instance arm_op_decl : asm_op_decl arm_op :=
  {|
    instr_desc_op := arm_instr_desc;
    prim_string := arm_prim_string;
  |}.

Definition arm_prog := @asm_prog _ _ _ _ _ _ _ arm_op_decl.
