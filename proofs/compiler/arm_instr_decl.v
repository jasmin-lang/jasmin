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
  values
  sopn
  arch_decl
  arch_utils.
Require Import arm_decl.


Module E.
  Definition no_semantics : error := ErrSemUndef.
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
| SBC                            (* Subtract with carry *)
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
  [:: ADD; ADC; MUL; MLA; MLS; SDIV; SUB; SBC; RSB; UDIV; UMULL; UMAAL; UMLAL; SMULL; SMLAL; SMMUL; SMMULR
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
  [:: ADD; ADC; MUL; SUB; SBC; RSB
    ; AND; BIC; EOR; MVN; ORR
    ; ASR; LSL; LSR; ROR
    ; MOV
  ].

Definition has_shift_mnemonics : seq arm_mnemonic :=
  [:: ADD; ADC; SUB; SBC; RSB
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
  | SBC => "SBC"
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
    else sem_prod_ok tout (sem_prod_tuple tout)
  in
  let f1 : sem_prod tin (sem_prod (sbool :: tout) (exec (sem_tuple tout))) :=
    sem_prod_app semi f0
  in
  add_arguments f1.

Lemma add_arguments_app t lt0 lt1 A (f : sem_prod (t::lt0) (sem_prod lt1 A)) v :
  add_arguments f v = add_arguments (f v).
Proof.
  move: f; rewrite /add_arguments /sem_prod /=.
  rewrite /eq_ind_r /eq_ind /=.
  move: (sem_prod_cat lt0 lt1 A); rewrite /sem_prod.
  move: (lprod [seq sem_t i | i <- lt0] (lprod [seq sem_t i | i <- lt1] A)) => T hT.
  subst T => //.
Qed.

Lemma mk_semi_cond_errty tin tout (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_forall (fun r : result error (sem_tuple tout) => r <> Error ErrType) tin semi ->
  sem_forall (fun r : result error (sem_tuple tout) => r <> Error ErrType) (tin ++ sbool :: tout)
                                      (mk_semi_cond semi).
Proof.
  rewrite /mk_semi_cond.
  elim: tin semi => /= [ | ti tin hrec] semi /=.
  + move=> hsemi [] /=; rewrite /add_arguments /= /eq_rect_r /= -/(exec (sem_tuple tout)).
    + by move: (sem_tuple tout) semi hsemi => /= T semi hsemi; elim: tout => //=.
    by apply: sem_prod_ok_error.
  move=> hsemi v; rewrite add_arguments_app; apply/hrec/hsemi.
Qed.

Lemma mk_semi_cond_safe tin tout sc (semi : sem_prod tin (exec (sem_tuple tout))) :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  interp_safe_cond_ty sc semi ->
  interp_safe_cond_ty sc (mk_semi_cond semi).
Proof.
  rewrite /interp_safe_cond_ty /mk_semi_cond /=.
  rewrite interp_safe_cond_ty_aux_cat => hsz.
  have {hsz} : all (fun sc => sc_needed_args sc <= size (@nil value) + size tin) sc by done.
  elim: tin (@nil value) semi => /= [ | t tin hrec] vs semi.
  + move=> hsz hall b /=; rewrite /add_arguments /= /eq_rect_r /=.
    case: b.
    + rewrite -cats1.
      move: (sem_tuple tout) semi hall => T semi hall.
      elim: tout [:: _] => /= [ | t' tout hrec].
      + move=> vs' /Forall_nthP h; apply/hall/Forall_nthP => sci i /[dup] hi /(h sci).
        apply interp_safe_cond_cat.
        by move/all_nthP: hsz => /(_ sci i hi); rewrite addn0.
      by move=> vs' v; rewrite -cats1 -catA; apply hrec.
    by apply: sem_prod_ok_safe_aux.
  move=> hall h1 v.
  have := hrec (rcons vs (to_val v)) (semi v) _ (h1 v).
  rewrite size_rcons addSnnS => /(_ hall).
  rewrite /eq_ind_r /eq_ind /= /add_arguments => {h1}.
  move: semi ; rewrite /sem_prod /= => semi.
  move: (sem_prod_cat _ _ _) semi; rewrite /sem_prod.
  move: (lprod [seq sem_t i | i <- tin ++ sbool :: tout] (exec (sem_tuple tout))) => ??; subst => /= semiv.
  rewrite /eq_rect_r /=; apply.
Qed.

Lemma safe_wf_cat (tin tin' : seq stype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof. apply sub_all => c h; rewrite size_cat; apply: (leq_trans h); apply leq_addr. Qed.

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
    id_valid := id_valid idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_semi_errty := fun h => mk_semi_cond_errty (idt.(id_semi_errty) h);
    id_semi_safe := fun h => mk_semi_cond_safe (id_safe_wf idt) (idt.(id_semi_safe) h);
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

Lemma mk_semi1_shifted_errty A sk (semi : sem_prod [:: sreg] (exec A)) :
  sem_forall (fun r : exec A => r <> Error ErrType) [:: sreg] semi ->
  sem_forall (fun r : exec A => r <> Error ErrType)
         ([:: sreg] ++ [:: sword8]) (mk_semi1_shifted sk semi).
Proof. by rewrite /mk_semi1_shifted /= => h *; apply h. Qed.

Lemma mk_semi2_2_shifted_errty A t sk (semi : sem_prod [:: t; sreg] (exec A)) :
  sem_forall (fun r : exec A => r <> Error ErrType) [:: t; sreg] semi ->
  sem_forall (fun r : exec A => r <> Error ErrType)
         ([:: t; sreg] ++ [:: sword8]) (mk_semi2_2_shifted sk semi).
Proof. rewrite /mk_semi2_2_shifted /= => h *; apply h. Qed.

Lemma mk_semi3_2_shifted_errty A t1 t2 sk (semi : sem_prod [:: t1; sreg; t2] (exec A)) :
  sem_forall (fun r : exec A => r <> Error ErrType) [:: t1; sreg; t2] semi ->
  sem_forall (fun r : exec A => r <> Error ErrType)
         ([:: t1; sreg; t2] ++ [:: sword8]) (mk_semi3_2_shifted sk semi).
Proof. rewrite /mk_semi3_2_shifted /= => h *; apply h. Qed.

Lemma mk_semi1_shifted_safe A sk (semi : sem_prod [:: sreg] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi1_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma mk_semi2_2_shifted_safe A sk t (semi : sem_prod [:: t; sreg] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi2_2_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma mk_semi3_2_shifted_safe A sk t1 t2 (semi : sem_prod [:: t1; sreg; t2] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi3_2_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Definition mk_shifted
  (sk : shift_kind) (idt : instr_desc_t) semi' semi_errty' semi_safe' : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: sword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm (CAimmC_arm_shift_amout sk) U8] ]) (id_args_kinds idt);
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
    id_valid := id_valid idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_semi_errty := semi_errty';
    id_semi_safe := semi_safe'
  |}.

Arguments mk_shifted : clear implicits.

Definition ak_reg_reg_imm_ ew :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm (CAimmC_arm_wencoding ew) reg_size]]].

Definition ak_reg_reg_imm_shift ws sk :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm (CAimmC_arm_shift_amout sk) ws]]].

Definition ak_reg_reg_reg_or_imm_ ew :=
  ak_reg_reg_reg ++ ak_reg_reg_imm_ ew.

Definition ak_reg_reg_reg_or_imm opts ew :=
  if has_shift opts then ak_reg_reg_reg else ak_reg_reg_reg_or_imm_ ew.

Definition ak_reg_imm_ ew :=
[:: [:: [:: CAreg]; [:: CAimm (CAimmC_arm_wencoding ew) reg_size]]].

Definition ak_reg_reg_or_imm_ ew :=
  ak_reg_reg ++ ak_reg_imm_ ew.

Definition ak_reg_reg_or_imm opts ew :=
  if has_shift opts then ak_reg_reg else ak_reg_reg_or_imm_ ew.

Definition chk_imm_accept_shift :=
  {| on_shift := WE_allowed true; on_none := WE_allowed false |}.

Definition chk_imm_accept_shift_w12 opts :=
  {| on_shift := WE_allowed true; on_none := if set_flags opts then WE_allowed false else W12_encoding |}.

Definition chk_imm_w16_encoding opts :=
  let allowed := if opts then WE_allowed false else W16_encoding in
  {| on_shift := allowed; on_none := allowed |}.

Definition chk_imm_reject_shift :=
  {| on_shift := WE_allowed false; on_none := WE_allowed false |}.

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

Definition arm_ADD_semi (wn wm : ty_r) : ty_nzcv_r :=
  let x :=
    nzcv_w_of_aluop
      (wn + wm)%R
      (wunsigned wn + wunsigned wm)%Z
      (wsigned wn + wsigned wm)%Z
  in
  x.

Definition arm_ADD_instr : instr_desc_t :=
  let mn := ADD in
  let tin := [:: sreg; sreg ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_ADD_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts (chk_imm_accept_shift_w12 opts);
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_ADD_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_ADD_semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_ADC_semi (wn wm : ty_r) (cf : bool) : ty_nzcv_r :=
  let c := Z.b2z cf in
  let x :=
    nzcv_w_of_aluop
      (wn + wm + wrepr reg_size c)%R
      (wunsigned wn + wunsigned wm + c)%Z
      (wsigned wn + wsigned wm + c)%Z
  in
  x.

Definition arm_ADC_instr : instr_desc_t :=
  let mn := ADC in
  let tin := [:: sreg; sreg; sbool ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; F CF ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_ADC_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_ADC_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_ADC_semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then
      mk_shifted sk x (mk_semi3_2_shifted sk (id_semi x))
                      (fun h => mk_semi3_2_shifted_errty (x.(id_semi_errty) h))
                      (fun h => mk_semi3_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_MUL_semi (wn wm : ty_r) : ty_nz_r :=
  let res := (wn * wm)%R in
  (:: Some (NF_of_word res), Some (ZF_of_word res) & res).

Definition arm_MUL_instr : instr_desc_t :=
  let mn := MUL in
  let tin := [:: sreg; sreg ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snz_r;
      id_out := ad_nz ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_MUL_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_MUL_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_MUL_semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nz x.

Definition arm_MLA_semi (wn wm wa: ty_r) : ty_r :=
  (wn * wm + wa)%R.

Definition arm_MLA_instr : instr_desc_t :=
  let mn := MLA in
  let tin := [:: sreg; sreg; sreg ] in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin ;
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_MLA_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_MLA_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_MLA_semi;
  |}.

Definition arm_MLS_semi (wn wm wa: ty_r) : ty_r :=
  (wa - wn * wm)%R.

Definition arm_MLS_instr : instr_desc_t :=
  let mn := MLS in
  let tin := [:: sreg; sreg; sreg ] in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: sreg ];
      id_out := [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_MLS_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_MLS_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_MLS_semi;
  |}.

(* We assume that DIV_0_TRP bit in the Configuration Control register is set to 0*)
Definition arm_SDIV_semi (wn wm : ty_r) : ty_r :=
  wdivi wn wm.

Definition arm_SDIV_instr : instr_desc_t :=
  let mn := SDIV in
  let tin :=[:: sreg; sreg ] in
  let semi := arm_SDIV_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [:: ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi
  |}.

Definition arm_SUB_semi (wn wm : ty_r) : ty_nzcv_r :=
  let wmnot := wnot wm in
  let x :=
    nzcv_w_of_aluop
      (wn + wmnot + 1)%R
      (wunsigned wn + wunsigned wmnot + 1)%Z
      (wsigned wn + wsigned wmnot + 1)%Z
  in
  x.

Definition arm_SUB_instr : instr_desc_t :=
  let mn := SUB in
  let tin := [:: sreg; sreg ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_SUB_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts (chk_imm_accept_shift_w12 opts);
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SUB_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SUB_semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_SBC_semi (wn wm : ty_r) (cf : bool) : ty_nzcv_r :=
  arm_ADC_semi wn (wnot wm) cf.

Definition arm_SBC_instr : instr_desc_t :=
  let mn := SBC in
  let tin := [:: sreg; sreg; sbool ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; F CF ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin arm_SBC_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SBC_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SBC_semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then
      mk_shifted sk x (mk_semi3_2_shifted sk (id_semi x))
                      (fun h => mk_semi3_2_shifted_errty (x.(id_semi_errty) h))
                      (fun h => mk_semi3_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_RSB_instr : instr_desc_t :=
  let mn := RSB in
  let tin := [:: sreg; sreg ] in
  let arm_RSB_semi := fun wn wm => arm_SUB_semi wm wn in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      (* The only difference with SUB is the order of the arguments. *)
      id_semi := sem_prod_ok tin arm_RSB_semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_RSB_semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_RSB_semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_UDIV_semi (wn wm : ty_r) : ty_r :=
  wdiv wn wm.

Definition arm_UDIV_instr : instr_desc_t :=
  let mn := UDIV in
  let tin := [:: sreg; sreg ] in
  let semi := arm_UDIV_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [:: ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_UMULL_semi (wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wumul wn wm in
  (lo, hi).

Definition arm_UMULL_instr : instr_desc_t :=
  let mn := UMULL in
  let tin := [:: sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := sem_prod_ok tin arm_UMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_UMULL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_UMULL_semi;
  |}.

Definition arm_UMAAL_semi (wa wb wn wm : ty_r) : ty_rr :=
  let r := (wunsigned wa + wunsigned wb + wunsigned wn * wunsigned wm)%Z in
  (wrepr reg_size r, high_bits reg_size r).

Definition arm_UMAAL_instr : instr_desc_t :=
  let mn := UMAAL in
  let tin := [:: sreg; sreg; sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := sem_prod_ok tin arm_UMAAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_UMAAL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_UMAAL_semi;
  |}.

Definition arm_UMLAL_semi (dlo dhi wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wumul wn wm in
  wdaddu dhi dlo hi lo.

Definition arm_UMLAL_instr : instr_desc_t :=
  let mn := UMLAL in
  let tin := [:: sreg; sreg; sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := sem_prod_ok tin arm_UMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_UMLAL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_UMLAL_semi;
  |}.

Definition arm_SMULL_semi (wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wsmul wn wm in
  (lo, hi).

Definition arm_SMULL_instr : instr_desc_t :=
  let mn := SMULL in
  let tin := [:: sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := sem_prod_ok tin arm_SMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SMULL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SMULL_semi;
  |}.

Definition arm_SMLAL_semi (dlo dhi wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wsmul wn wm in
  wdadds dhi dlo hi lo.

Definition arm_SMLAL_instr : instr_desc_t :=
  let mn := SMLAL in
  let tin := [:: sreg; sreg; sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg; sreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi := sem_prod_ok tin arm_SMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SMLAL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SMLAL_semi;
  |}.

Definition arm_SMMUL_semi (wn wm : ty_r) : ty_r :=
  wmulhs wn wm.

Definition arm_SMMUL_instr : instr_desc_t :=
  let mn := SMMUL in
  let tin := [:: sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0];
    id_semi := sem_prod_ok tin arm_SMMUL_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SMMUL_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SMMUL_semi;
  |}.

Definition arm_SMMULR_semi (wn wm : ty_r) : ty_r :=
  high_bits reg_size (wsigned wn * wsigned wm + 0x80000000).

Definition arm_SMMULR_instr : instr_desc_t :=
  let mn := SMMULR in
  let tin := [:: sreg; sreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0];
    id_semi := sem_prod_ok tin arm_SMMULR_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) arm_SMMULR_semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) arm_SMMULR_semi;
  |}.

Definition get_hw (hw : halfword) (x : wreg) : u16 :=
  if split_vec 16 x is [:: lo; hi ]
  then if hw is HWT then hi else lo
  else 0%R. (* Never happens. *)

Definition arm_smul_hw_semi (hwn hwm : halfword) (wn wm : wreg) : wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m)%Z in
  wrepr U32 r.

Definition arm_smul_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMUL_hw hwn hwm in
  let tin := [:: sreg; sreg ] in
  let semi := arm_smul_hw_semi hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_smla_hw_semi
  (hwn hwm : halfword) (wn wm acc : wreg) : wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m + wsigned acc)%Z in
  wrepr U32 r.

Definition arm_smla_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMLA_hw hwn hwm in
  let tin := [:: sreg; sreg; sreg ] in
  let semi := arm_smla_hw_semi hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_smulw_hw_semi (hw : halfword) (wn wm : wreg) : wreg :=
  let m := get_hw hw wm in
  let res := (wsigned wn * wsigned m)%Z in
  let w := wrepr U64 res in
  winit U32 (fun i => wbit_n w (i + 16)).

Definition arm_smulw_hw_instr hw : instr_desc_t :=
  let mn := SMULW_hw hw in
  let tin := [:: sreg; sreg ] in
  let semi := arm_smulw_hw_semi hw in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_bitwise_semi
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : ty_w ws) :
  ty_nzc_w ws :=
  let res := op (op0 wn) (op1 wm) in
  (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , None (* TODO_ARM: Complete. C depends on the shift. *)
       & res
     ).

Definition arm_AND_instr : instr_desc_t :=
  let mn := AND in
  let tin := [:: sreg; sreg ] in
  let semi := arm_bitwise_semi id id wand in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
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

Definition arm_BFC_semi_sc := [:: ULt U8 1 32%Z; UGe U8 1%Z 2; UaddLe U8 2 1 32%Z].

Lemma arm_BFC_semi_errty :
  sem_forall (fun r : result error (sem_tuple  [:: sreg ]) => r <> Error ErrType)
   [:: sreg; sword8; sword8 ] arm_BFC_semi.
Proof.
  rewrite /arm_BFC_semi => x lsb width.
  by case: (_ <? _)%Z => //; case: (1 <=? _)%Z => //; case: (_ <=? _)%Z.
Qed.

Lemma arm_BFC_semi_safe :
  interp_safe_cond_ty (tin :=[:: sreg; sword8; sword8 ]) arm_BFC_semi_sc arm_BFC_semi.
Proof.
  rewrite /interp_safe_cond_ty /= => x lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h3 _ /(_ _ erefl) /ZleP h2 /(_ _ erefl) /ZltP h1.
  have /ZleP {}h3 : (wunsigned width <= 32 - wunsigned lsb)%Z by Lia.lia.
  rewrite /arm_BFC_semi h1 h2 h3 /=; eauto.
Qed.

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
    id_safe := arm_BFC_semi_sc;
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => arm_BFC_semi_errty;
    id_semi_safe := fun _ => arm_BFC_semi_safe;
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

Definition arm_BFI_semi_sc := [:: ULt U8 2 32%Z; UGe U8 1%Z 3; UaddLe U8 3 2 32%Z].

Lemma arm_BFI_semi_errty :
  sem_forall (fun r : result error (sem_tuple  [:: sreg ]) => r <> Error ErrType)
   [:: sreg; sreg; sword8; sword8 ] arm_BFI_semi.
Proof.
  rewrite /arm_BFI_semi => x y lsb width.
  by case: (_ <? _)%Z => //; case: (1 <=? _)%Z => //; case: (_ <=? _)%Z.
Qed.

Lemma arm_BFI_semi_safe :
  interp_safe_cond_ty (tin :=[:: sreg; sreg; sword8; sword8 ]) arm_BFI_semi_sc arm_BFI_semi.
Proof.
  rewrite /interp_safe_cond_ty /= => x y lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h3 _ /(_ _ erefl) /ZleP h2 /(_ _ erefl) /ZltP h1.
  have /ZleP {}h3 : (wunsigned width <= 32 - wunsigned lsb)%Z by Lia.lia.
  rewrite /arm_BFI_semi h1 h2 h3 /=; eauto.
Qed.

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
    id_safe := arm_BFI_semi_sc;
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => arm_BFI_semi_errty;
    id_semi_safe := fun _ => arm_BFI_semi_safe;
  |}.

Definition arm_BIC_instr : instr_desc_t :=
  let mn := BIC in
  let tin := [:: sreg; sreg ] in
  let semi := arm_bitwise_semi id wnot wand in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_EOR_instr : instr_desc_t :=
  let mn := EOR in
  let tin := [:: sreg; sreg ] in
  let semi := arm_bitwise_semi id id wxor in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_MVN_semi (wn : ty_r) : ty_nzc_r :=
  let res := wnot wn in
  (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , None (* TODO_ARM: Complete. C depends on the shift. *)
       & res
     ).

Definition arm_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let tin := [:: sreg ] in
  let semi := arm_MVN_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi1_shifted sk (id_semi x))
                         (fun h => mk_semi1_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi1_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ORR_instr : instr_desc_t :=
  let mn := ORR in
  let tin := [:: sreg; sreg ] in
  let semi := arm_bitwise_semi id id wor in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                         (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                         (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_shift_semi
  (op : ty_r -> Z -> ty_r) (op_c : ty_r -> Z -> bool)
  (wn : ty_r) (wsham : word U8) : ty_nzc_r :=
  let sham := wunsigned wsham in
  let res := op wn sham in
  if sham == 0%Z then
    (* This is under specified compared to real arm semantics *)
    (:: None, None, None & res)
  else
    (:: Some (NF_of_word res)
      , Some (ZF_of_word res)
      , Some (op_c wn sham)
      & res
     ).

Definition arm_ASR_C (wn : ty_r) (shift : Z) :=
  if (32 <=? shift)%Z then msb wn
  else wbit_n wn (32 - Z.to_nat (shift - 1)).

Definition arm_ASR_semi (wn : ty_r) (wsham : word U8) : ty_nzc_r :=
  (* The bounds for [wsham] are different whether it's an immediate or a
     register: if it's an immediate it must be between 0 and 31, but if it's a
     register it must be between 0 and 255 (the lower byte of the register).
     Since registers only 32 bits it makes no difference. *)
  arm_shift_semi (@wsar _) arm_ASR_C wn wsham.

Definition arm_ASR_instr : instr_desc_t :=
  let mn := ASR in
  let tin := [:: sreg; sword U8 ] in
  let semi := arm_ASR_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SASR;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSL_C (wn : ty_r) (shift: Z) :=
  if (shift <=? 32)%Z then wbit_n wn (32-Z.to_nat shift)
  else false.

Definition arm_LSL_semi (wn : ty_r) (wsham : word U8) : ty_nzc_r :=
  arm_shift_semi (@wshl _) arm_LSL_C wn wsham.

Definition arm_LSL_instr : instr_desc_t :=
  let mn := LSL in
  let tin := [:: sreg; sword U8 ] in
  let semi := arm_LSL_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SLSL;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSR_C (wn : ty_r) (shift : Z) :=
  if (32 <=? shift)%Z then false
  else wbit_n wn (32-Z.to_nat (shift - 1)).

Definition arm_LSR_semi (wn : ty_r) (wsham : word U8) : ty_nzc_r :=
  arm_shift_semi (@wshr _) arm_LSR_C wn wsham.

Definition arm_LSR_instr : instr_desc_t :=
  let mn := LSR in
  let tin := [:: sreg; sword U8 ] in
  let semi := arm_LSR_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SLSR;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ROR_C (wn : ty_r) (shift : Z) :=
  let res := wror wn shift in
  msb res.

Definition arm_ROR_semi (wn : ty_r) (wsham : word U8) : ty_nzc_r :=
  arm_shift_semi (@wror _) arm_ROR_C wn wsham.

Definition arm_ROR_instr : instr_desc_t :=
  let mn := ROR in
  let tin := [:: sreg; sword U8 ] in
  let semi := arm_ROR_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi ;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SROR;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition mk_rev_instr mn semi :=
  let tin := [:: sreg ] in
  {| id_msb_flag := MSB_MERGE
   ; id_tin := tin
   ; id_in := [:: Ea 1 ]
   ; id_tout := [:: sreg]
   ; id_out := [:: Ea 0 ]
   ; id_semi := sem_prod_ok tin semi
   ; id_nargs := 2
   ; id_args_kinds := ak_reg_reg
   ; id_eq_size := refl_equal
   ; id_tin_narr := refl_equal
   ; id_tout_narr := refl_equal
   ; id_check_dest := refl_equal
   ; id_str_jas := pp_s (string_of_arm_mnemonic mn)
   ; id_safe := [::]
   ; id_pp_asm := pp_arm_op mn opts
   ; id_valid := true
   ; id_safe_wf := refl_equal
   ; id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _
   ; id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi
  |}.

Definition arm_REV_semi (w : ty_r) : ty_r :=
  wbswap w.

Definition arm_REV16_semi (w : ty_r) : ty_r :=
  lift1_vec U16 (@wbswap U16) U32 w.

Definition arm_REVSH_semi (w : ty_r) : ty_r :=
  sign_extend U32 (wbswap (zero_extend U16 w)).

Definition arm_REV_instr   := mk_rev_instr REV   arm_REV_semi.
Definition arm_REV16_instr := mk_rev_instr REV16 arm_REV16_semi.
Definition arm_REVSH_instr := mk_rev_instr REVSH arm_REVSH_semi.

Definition arm_ADR_semi (wn: ty_r) : ty_r :=
  wn.

Definition arm_ADR_instr : instr_desc_t :=
  let mn := ADR in
  let tin := [:: sreg ] in
  let semi := arm_ADR_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ec 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_MOV_semi (wn : ty_r) : ty_nzc_r :=
  (:: Some (NF_of_word wn), Some (ZF_of_word wn), None (* TODO_ARM: Complete *) & wn).

Definition arm_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let tin := [:: sreg ] in
  let semi := arm_MOV_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi := sem_prod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm_ (chk_imm_w16_encoding opts.(set_flags));
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_MOVT_semi (wn : ty_r) (wm : word U16) : ty_r :=
  let hi := wshl (zero_extend reg_size wm) 16 in
  let mask := zero_extend reg_size (wrepr U16 (-1)) in
  wor hi (wand wn mask).

Definition arm_MOVT_instr : instr_desc_t :=
  let mn := MOVT in
  let tin := [:: sreg; sword U16 ] in
  let semi := arm_MOVT_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ] ] ];
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition bit_field_extract_semi
  (shr : wreg -> Z -> wreg) (wn : wreg) (widx wwidth : word U8) : exec wreg :=
  let idx := wunsigned widx in
  let width := wunsigned wwidth in
  Let _ := assert [&& 1 <=? width & width <? 33-idx]%Z E.no_semantics in
  ok (shr (wshl wn (32 - width - idx)%Z) (32 - width)%Z).

Definition bit_field_extract_semi_sc := [:: UGe U8 1%Z 2; UaddLe U8 2 1 32%Z].

Lemma bit_field_extract_semi_errty shr :
  sem_forall (fun r : result error (sem_tuple  [:: sreg ]) => r <> Error ErrType)
   [:: sreg; sword8; sword8 ] (bit_field_extract_semi shr).
Proof. by rewrite /bit_field_extract_semi => x lsb width; case: andP. Qed.

Lemma bit_field_extract_semi_safe shr :
  interp_safe_cond_ty (tin :=[:: sreg; sword8; sword8 ]) bit_field_extract_semi_sc (bit_field_extract_semi shr).
Proof.
  rewrite /interp_safe_cond_ty /= => x lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h2 _ /(_ _ erefl) /ZleP h1.
  have /ZltP {}h2 : (wunsigned width < 33 - wunsigned lsb)%Z by Lia.lia.
  rewrite /bit_field_extract_semi h1 h2 /=; eauto.
Qed.

Definition ak_reg_reg_imm_imm_extr :=
   [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (CAimmC_arm_shift_amout SLSL) U8 ]; [:: CAimm_sz U8 ] ] ].

Definition arm_UBFX_instr : instr_desc_t :=
  let mn := UBFX in
  let sh := (wshr (sz := reg_size)) in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8; sword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := bit_field_extract_semi sh;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm_imm_extr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := bit_field_extract_semi_sc;
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => @bit_field_extract_semi_errty sh;
    id_semi_safe := fun _ => @bit_field_extract_semi_safe sh;
  |}.

Definition extend_bits_semi
  (len : Z) (wn : wreg) (wroram : word U8) : wreg :=
  let mask := wrepr reg_size (2 ^ len - 1)%Z in
  let roram := wunsigned wroram in
  wand mask (wror wn roram).

Definition ak_reg_reg_imm8_0_8_16_24 :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm CAimmC_arm_0_8_16_24 U8]]].

Definition arm_UXTB_instr : instr_desc_t :=
  let mn := UXTB in
  let tin := [:: sreg; sword U8 ] in
  let semi := extend_bits_semi 8 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_UXTH_instr : instr_desc_t :=
  let mn := UXTH in
  let tin := [:: sreg; sword U8 ] in
  let semi := extend_bits_semi 16 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi := sem_prod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_SBFX_instr : instr_desc_t :=
  let mn := SBFX in
  let sh := (wsar (sz := reg_size)) in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sword U8; sword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    (* [0 <= widx < 32] is enforced in args_kinds
       [1 <= wwidth < 33-widx] is enforced by the instruction
       TODO : a safety condition should be added
    *)
    id_semi := bit_field_extract_semi sh;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm_imm_extr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := bit_field_extract_semi_sc;
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => @bit_field_extract_semi_errty sh;
    id_semi_safe := fun _ => @bit_field_extract_semi_safe sh;
  |}.

Definition arm_CMP_semi (wn wm : ty_r) : ty_nzcv :=
  let wmnot := wnot wm in
  nzcv_of_aluop
      (wn + wmnot + 1)%R
      (wunsigned wn + wunsigned wmnot + 1)%Z
      (wsigned wn + wsigned wmnot + 1)%Z.

Definition arm_CMP_instr : instr_desc_t :=
  let mn := CMP in
  let tin := [:: sreg; sreg ] in
  let semi := arm_CMP_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := sem_prod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

Definition arm_TST_semi (wn wm : ty_r) : ty_nzc :=
  let res := wand wn wm in
  (:: Some (NF_of_word res)
      , Some (ZF_of_word res)
      & Some false             (* TODO_ARM: C depends on shift or immediate. *)
    ).

Definition arm_TST_instr : instr_desc_t :=
  let mn := TST in
  let tin := [:: sreg; sreg ] in
  let semi := arm_TST_semi in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzc;
      id_out := ad_nzc;
      id_semi := sem_prod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

Definition arm_CMN_instr : instr_desc_t :=
  let mn := CMN in
  let tin := [:: sreg; sreg ] in
  let semi := fun wn wm => rtuple_drop5th (arm_ADD_semi wn wm) in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := sem_prod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
      id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

Definition arm_extend_semi
  {ws : wsize} (sign : bool) (ws' : wsize) (wn : word ws) : word ws' :=
  let f := if sign then sign_extend else zero_extend in
  (f ws' ws wn).

Definition arm_load_instr mn : instr_desc_t :=
  let ws :=
    if wsize_of_load_mn mn is Some ws'
    then ws'
    else U32 (* Never happens. *)
  in
  let tin := [:: sword ws ] in
  let semi := arm_extend_semi (isSome (wsize_of_sload_mn mn)) reg_size in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_store_instr mn : instr_desc_t :=
  let ws :=
    if wsize_of_store_mn mn is Some ws'
    then ws'
    else U32 (* Never happens. *)
  in
  let tin := [:: sword ws ] in
  let semi := arm_extend_semi false ws in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be a [reg_size] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: sword ws ];
    id_out := [:: Eu 1 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
  |}.

Definition arm_CLZ_instr :=
  let mn := CLZ in
  let tin := [:: sreg ] in
  let semi := fun z => leading_zero z in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: sreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_prod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_prod_ok_error (tin:=tin) semi _;
    id_semi_safe := fun _ => sem_prod_ok_safe (tin:=tin) semi;
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
  | SBC => arm_SBC_instr
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
