(* ARM Cortex-M4 instruction set

   These are the THUMB instructions of ARMv7-M, the instruction set of the M4
   processor. *)

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
  sopn_semi
  arch_decl
  arch_utils.
Require Import arm_decl.

Module E.
  (* Error of the instructions whose arguments are out of range (BFC, BFI,
     UBFX, SBFX). It is the [id_err] of those descriptors, raised when one of
     the [id_safe] conditions describing exactly these cases fails. *)
  Definition no_semantics : error := ErrSemUndef.
End E.

(* -------------------------------------------------------------------- *)
(* ARM instruction options. *)

#[only(eqbOK)] derive
Record arm_options :=
  {
    set_flags : bool;
    is_conditional : bool;
    has_shift : option shift_kind;
  }.

#[ export ]
Instance eqTC_arm_options : eqTypeC arm_options :=
  { ceqP := arm_options_eqb_OK }.

Canonical arm_options_eqType := @ceqT_eqType _ eqTC_arm_options.

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

#[only(eqbOK)] derive
Variant halfword : Type :=
| HWB
| HWT
.

#[only(eqbOK)] derive
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
| SXTB                           (* Extract a byte and sign extend *)
| SXTH                           (* Extract a halfword and sign extend *)
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

#[ export ]
Instance eqTC_arm_mnemonic : eqTypeC arm_mnemonic :=
  { ceqP := arm_mnemonic_eqb_OK }.

Canonical arm_mnemonic_eqType := @ceqT_eqType _ eqTC_arm_mnemonic.

Definition arm_mnemonics : seq arm_mnemonic :=
  [:: ADD; ADC; MUL; MLA; MLS; SDIV; SUB; SBC; RSB; UDIV; UMULL; UMAAL; UMLAL; SMULL; SMLAL; SMMUL; SMMULR
    ; SMUL_hw HWB HWB; SMUL_hw HWB HWT; SMUL_hw HWT HWB; SMUL_hw HWT HWT
    ; SMLA_hw HWB HWB; SMLA_hw HWB HWT; SMLA_hw HWT HWB; SMLA_hw HWT HWT
    ; SMULW_hw HWB; SMULW_hw HWT
    ; AND; BFC; BFI; BIC; EOR; MVN; ORR
    ; ASR; LSL; LSR; ROR; REV; REV16; REVSH
    ; ADR; MOV; MOVT; UBFX; UXTB; UXTH; SBFX; SXTB; SXTH; CLZ
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
  [:: (UXTB, SROR); (UXTH, SROR); (SXTB, SROR); (SXTH, SROR) ].

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
  | SXTB => "SXTB"
  | SXTH => "SXTH"
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

#[only(eqbOK)] derive
Variant arm_op :=
| ARM_op : arm_mnemonic -> arm_options -> arm_op.

#[ export ]
Instance eqTC_arm_op : eqTypeC arm_op :=
  { ceqP := arm_op_eqb_OK }.

Canonical arm_op_eqType := @ceqT_eqType _ eqTC_arm_op.

(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sflag := (lbool) (only parsing).
Notation snz := ([:: sflag; sflag ]) (only parsing).
Notation snzc := ([:: sflag; sflag; sflag ]) (only parsing).
Notation snzcv := ([:: sflag; sflag; sflag; sflag ]) (only parsing).
Notation snz_r := (snz ++ [:: lreg ]) (only parsing).
Notation snzc_r := (snzc ++ [:: lreg ]) (only parsing).
Notation snzcv_r := (snzcv ++ [:: lreg ]) (only parsing).

Notation ty_nzcv := (sem_ltuple snzcv) (only parsing).
Notation ty_r := (sem_ltuple [:: lreg ]) (only parsing).
Notation ty_rr := (sem_ltuple [:: lreg; lreg ]) (only parsing).
Notation ty_w ws := (sem_ltuple [:: lword ws ]) (only parsing).

Notation ty_nzcv_w ws := (sem_ltuple (snzcv ++ [:: lword ws ])) (only parsing).

(* Counterparts of the above for the total semantics, where a flag is a
   [bool] and not an [option bool]. *)
Notation ty_nzc_t := (sem_ltuple_t snzc) (only parsing).
Notation ty_nzcv_t := (sem_ltuple_t snzcv) (only parsing).
Notation ty_w_t ws := (sem_ltuple_t [:: lword ws ]) (only parsing).
Notation ty_nz_r_t := (sem_ltuple_t (snz ++ [:: lreg ])) (only parsing).
Notation ty_nzc_r_t := (sem_ltuple_t (snzc ++ [:: lreg ])) (only parsing).
Notation ty_nzcv_r_t := (sem_ltuple_t (snzcv ++ [:: lreg ])) (only parsing).

(* -------------------------------------------------------------------- *)
(* Common argument descriptions.*)

Definition ad_nz : seq arg_desc := map F [:: NF; ZF ].
Definition ad_nzc : seq arg_desc := map F [:: NF; ZF; CF ].
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

Definition nzcv_w_of_aluop {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop w wun wsi) (w : ty_w ws).

(* Total counterparts: all four flags are defined. *)
Definition nzcv_of_aluop_t
  {ws : wsize} (res : word ws) (res_unsigned res_signed : Z) : ty_nzcv_t :=
  (:: NF_of_word res
    , ZF_of_word res
    , wunsigned res != res_unsigned
    & wsigned res != res_signed
  ).

Definition nzcv_w_of_aluop_t {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop_t w wun wsi) (w : ty_w_t ws).

(* Total counterpart of [arch_utils.rtuple_drop5th]. *)
Definition rtuple_drop5th_t
  {t0 t1 t2 t3 t4 : ctype}
  (xs : sem_tuple_t [:: t0; t1; t2; t3; t4 ]) : sem_tuple_t [:: t0; t1; t2; t3 ] :=
  let: (:: x0, x1, x2, x3 & x4 ) := xs in
  (:: x0, x1, x2 & x3 ).

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

Definition sem_lprod_cat lt0 lt1 A :
  sem_lprod (lt0 ++ lt1) A = sem_lprod lt0 (sem_lprod lt1 A).
Proof.
  induction lt0 as [|t lt0' IH];
    first done.
  rewrite /sem_prod /=.
  rewrite /sem_prod in IH.
  by rewrite IH.
Defined.

Definition add_arguments {A} {lt0 lt1} (f: sem_lprod lt0 (sem_lprod lt1 A))
  : sem_lprod (lt0 ++ lt1) A.
Proof.
  rewrite sem_lprod_cat.
  by apply: f.
Defined.

Definition mk_semi_cond tin tout (semi : sem_lprod tin (exec (sem_ltuple tout)))
  : sem_lprod (tin ++ lbool :: tout) (exec (sem_ltuple tout)) :=
  let f0 res cond : sem_lprod tout (exec (sem_ltuple tout)) :=
    if cond
    then sem_prod_const (map eval_ltype tout) res
    else sem_prod_ok (map eval_ltype tout) (sem_prod_tuple (map eval_ltype tout))
  in
  let f1 : sem_lprod tin (sem_lprod (lbool :: tout) (exec (sem_ltuple tout))) :=
    sem_prod_app semi f0
  in
  add_arguments f1.

Definition mk_semi_cond_t tin tout (f : sem_lprod tin (sem_ltuple_t tout))
  : sem_lprod (tin ++ lbool :: tout) (sem_ltuple_t tout) :=
  let f0 res cond : sem_lprod tout (sem_ltuple_t tout) :=
    if cond
    then sem_prod_const (map eval_ltype tout) res
    else sem_prod_tuple_t (map eval_ltype tout)
  in
  let f1 : sem_lprod tin (sem_lprod (lbool :: tout) (sem_ltuple_t tout)) :=
    sem_prod_app f f0
  in
  add_arguments f1.

Lemma safe_wf_cat (tin tin' : seq ltype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof. apply sub_all => c h; rewrite size_cat; apply: (leq_trans h); apply leq_addr. Qed.

(* Guarding a condition adds a dependency on the guard, which is the argument
   just after those of the unconditional instruction. *)
Lemma mk_cond_safe_wf (idt : instr_desc_t) :
  all (fun sc => sc_needed_args sc <= size (id_tin idt ++ lbool :: id_tout idt))
      (map (Guarded (size (id_tin idt))) (id_safe idt)).
Proof.
  have h := all_sc_needed_args_guarded (id_safe_wf idt).
  apply: sub_all h => sc hsc; apply: leq_trans hsc _.
  by rewrite size_cat /= addnS ltnS leq_addr.
Qed.

(* The initialisation conditions of the conditional instruction are those of
   the unconditional one, under the guard. *)
Lemma mk_cond_wf (idt : instr_desc_t) :
  [&& all (safety_cond_wf (map eval_ltype (id_tin idt ++ lbool :: id_tout idt)))
        (map (cond_init (size (id_tin idt))) (id_init idt)),
      ssrnat.eqn (size (map (cond_init (size (id_tin idt))) (id_init idt)))
                 (size (id_tout idt))
    & ~~ is_ErrType (id_err idt)].
Proof.
  have /and3P [h1 h2 h3] := id_wf idt.
  rewrite size_map h2 h3 !andbT map_cat /= all_map.
  apply: sub_all h1 => c hc.
  by have := safety_cond_wf_cond_init (map eval_ltype (id_tout idt)) hc; rewrite size_map.
Qed.

Definition mk_cond (idt : instr_desc_t) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ lbool :: (id_tout idt);
    id_in := (id_in idt) ++ Ea (id_nargs idt) :: (id_out idt);
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi_total := mk_semi_cond_t (id_semi_total idt);
    id_nargs := (id_nargs idt).+1;
    id_args_kinds := map (fun x => x ++ [:: [:: CAcond ] ]) (id_args_kinds idt);
    id_eq_size := mk_cond_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    (* [mk_semi_cond] does not run the guarded instruction when the guard is
       false, so its conditions are those of [idt] under the guard. *)
    id_safe := map (Guarded (size (id_tin idt))) (id_safe idt);
    id_err := id_err idt;
    id_init := map (cond_init (size (id_tin idt))) (id_init idt);
    id_pp_asm := id_pp_asm idt;
    id_valid := id_valid idt;
    id_doit := id_doit idt;
    id_safe_wf := mk_cond_safe_wf idt;
    id_wf := mk_cond_wf idt;
  |}.
Arguments mk_cond : clear implicits.

(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Definition mk_semi1_shifted
  {A} (sk : shift_kind) (semi : sem_lprod [:: lreg ] (exec A)) :
  sem_lprod [:: lreg; lword8 ] (exec A) :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted
  {A} {o : ltype} (sk : shift_kind) (semi : sem_lprod [:: o; lreg ] (exec A)) :
  sem_lprod [:: o; lreg; lword8 ] (exec A) :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

(* Same, for a total semantics (no [exec] on the result). *)
Definition mk_semi1_shifted_t
  {A} (sk : shift_kind) (semi : sem_lprod [:: lreg ] A) :
  sem_lprod [:: lreg; lword8 ] A :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted_t
  {A} {o : ltype} (sk : shift_kind) (semi : sem_lprod [:: o; lreg ] A) :
  sem_lprod [:: o; lreg; lword8 ] A :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

Definition mk_semi3_2_shifted_t
  {A} {o0 o1 : ltype} (sk : shift_kind) (semi : sem_lprod [:: o0; lreg; o1 ] A) :
  sem_lprod [:: o0; lreg; o1; lword8 ] A :=
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

Lemma shifted_wf (idt : instr_desc_t) :
  [&& all (safety_cond_wf (map eval_ltype (id_tin idt ++ [:: lword8 ]))) (id_init idt),
      ssrnat.eqn (size (id_init idt)) (size (id_tout idt))
    & ~~ is_ErrType (id_err idt)].
Proof.
  have /and3P [h1 h2 h3] := id_wf idt.
  by rewrite map_cat (all_safety_cond_wf_cat _ h1) h2 h3.
Qed.

Definition mk_shifted
  (sk : shift_kind) (idt : instr_desc_t) semi_total' : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi_total := semi_total';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm (Some (CAimmC_arm_shift_amout sk)) U8] ]) (id_args_kinds idt);
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_err := id_err idt;
    id_init := id_init idt;
    id_pp_asm := id_pp_asm idt;
    id_valid := id_valid idt;
    id_doit := id_doit idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_wf := shifted_wf idt;
  |}.

Arguments mk_shifted : clear implicits.

Definition ak_reg_reg_imm_ ew :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm (Some (CAimmC_arm_wencoding ew)) reg_size]]].

Definition ak_reg_reg_imm_shift ws sk :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm (Some (CAimmC_arm_shift_amout sk)) ws]]].

Definition ak_reg_reg_reg_or_imm_ ew :=
  ak_reg_reg_reg ++ ak_reg_reg_imm_ ew.

Definition ak_reg_reg_reg_or_imm opts ew :=
  if has_shift opts then ak_reg_reg_reg else ak_reg_reg_reg_or_imm_ ew.

Definition ak_reg_imm_ ew :=
[:: [:: [:: CAreg]; [:: CAimm (Some (CAimmC_arm_wencoding ew)) reg_size]]].

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

   The argument type for shifts is [lword U8] and we must enforce that the
   value is in the appropriate range.
   It can't be "int" since only words have an interpretation.

   All descriptions have [id_msb_flag] as [MSB_MERGE], but since all
   instructions have a 32-bit output, this is irrelevant. *)

Section ARM_INSTR.

Context
  (opts : arm_options).

Let string_of_arm_mnemonic mn :=
      (string_of_arm_mnemonic mn
        ++ (if set_flags opts then "S" else "")
        ++ (if is_conditional opts then "cc" else ""))%string.

Definition arm_ADD_semi_t (wn wm : ty_r) : ty_nzcv_r_t :=
  nzcv_w_of_aluop_t
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

Definition arm_ADD_instr : instr_desc_t :=
  let mn := ADD in
  let tin := [:: lreg; lreg ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi_total := arm_ADD_semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts (chk_imm_accept_shift_w12 opts);
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_ADC_semi_t (wn wm : ty_r) (cf : bool) : ty_nzcv_r_t :=
  let c := Z.b2z cf in
  nzcv_w_of_aluop_t
    (wn + wm + wrepr reg_size c)%w
    (wunsigned wn + wunsigned wm + c)%Z
    (wsigned wn + wsigned wm + c)%Z.

Definition arm_ADC_instr : instr_desc_t :=
  let mn := ADC in
  let tin := [:: lreg; lreg; lbool ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; F CF ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi_total := arm_ADC_semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then
      mk_shifted sk x (mk_semi3_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_MUL_semi_t (wn wm : ty_r) : ty_nz_r_t :=
  let res := (wn * wm)%w in
  (:: NF_of_word res, ZF_of_word res & res).

(* Registers that cannot be encoded using three bits and are therefore unusable with MULS *)
Definition arm_high_registers : seq register :=
  [:: R08; R09; R10; R11; R12; LR ].

Definition arm_MUL_instr : instr_desc_t :=
  let mn := MUL in
  let tin := [:: lreg; lreg ] in
  let iop n :=
    if set_flags opts then
      ADExplicit (AK_mem Aligned) n (ACR_subset arm_high_registers)
    else Ea n.+1 in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: iop 0; iop 1 ];
      id_tout := snz_r;
      id_out := ad_nz ++ [:: Ea 0 ];
      id_semi_total := arm_MUL_semi_t;
      id_nargs := if set_flags opts then 2 else 3;
      id_args_kinds := if set_flags opts then ak_reg_reg else ak_reg_reg_reg;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if set_flags opts
  then x
  else drop_nz x.

Definition arm_MLA_semi (wn wm wa: ty_r) : ty_r :=
  (wn * wm + wa)%w.

Definition arm_MLA_instr : instr_desc_t :=
  let mn := MLA in
  let tin := [:: lreg; lreg; lreg ] in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin ;
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: lreg ];
      id_out := [:: Ea 0 ];
      id_semi_total := arm_MLA_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
  |}.

Definition arm_MLS_semi (wn wm wa: ty_r) : ty_r :=
  (wa - wn * wm)%w.

Definition arm_MLS_instr : instr_desc_t :=
  let mn := MLS in
  let tin := [:: lreg; lreg; lreg ] in
  {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; Ea 3 ];
      id_tout := [:: lreg ];
      id_out := [:: Ea 0 ];
      id_semi_total := arm_MLS_semi;
      id_nargs := 4;
      id_args_kinds := ak_reg_reg_reg_reg;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
  |}.

(* We assume that DIV_0_TRP bit in the Configuration Control register is set to 0*)
Definition arm_SDIV_semi (wn wm : ty_r) : ty_r :=
  wdivi wn wm.

Definition arm_SDIV_instr : instr_desc_t :=
  let mn := SDIV in
  let tin :=[:: lreg; lreg ] in
  let semi := arm_SDIV_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [:: ];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SUB_semi_t (wn wm : ty_r) : ty_nzcv_r_t :=
  let wmnot := wnot wm in
  nzcv_w_of_aluop_t
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

Definition arm_SUB_instr : instr_desc_t :=
  let mn := SUB in
  let tin := [:: lreg; lreg ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi_total := arm_SUB_semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts (chk_imm_accept_shift_w12 opts);
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_SBC_semi_t (wn wm : ty_r) (cf : bool) : ty_nzcv_r_t :=
  arm_ADC_semi_t wn (wnot wm) cf.

Definition arm_SBC_instr : instr_desc_t :=
  let mn := SBC in
  let tin := [:: lreg; lreg; lbool ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2; F CF ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi_total := arm_SBC_semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then
      mk_shifted sk x (mk_semi3_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_RSB_instr : instr_desc_t :=
  let mn := RSB in
  let tin := [:: lreg; lreg ] in
  let arm_RSB_semi_t := fun wn wm => arm_SUB_semi_t wm wn in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv_r;
      id_out := ad_nzcv ++ [:: Ea 0 ];
      (* The only difference with SUB is the order of the arguments. *)
      id_semi_total := arm_RSB_semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := NOT_DOIT; (* Not DIT *)
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_UDIV_semi (wn wm : ty_r) : ty_r :=
  wdiv wn wm.

Definition arm_UDIV_instr : instr_desc_t :=
  let mn := UDIV in
  let tin := [:: lreg; lreg ] in
  let semi := arm_UDIV_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [:: ];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_UMULL_semi (wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wumul wn wm in
  (lo, hi).

Definition arm_UMULL_instr : instr_desc_t :=
  let mn := UMULL in
  let tin := [:: lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: lreg; lreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := arm_UMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true; IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_UMAAL_semi (wa wb wn wm : ty_r) : ty_rr :=
  let r := (wunsigned wa + wunsigned wb + wunsigned wn * wunsigned wm)%Z in
  (wrepr reg_size r, high_bits reg_size r).

Definition arm_UMAAL_instr : instr_desc_t :=
  let mn := UMAAL in
  let tin := [:: lreg; lreg; lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg; lreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := arm_UMAAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true; IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_UMLAL_semi (dlo dhi wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wumul wn wm in
  wdaddu dhi dlo hi lo.

Definition arm_UMLAL_instr : instr_desc_t :=
  let mn := UMLAL in
  let tin := [:: lreg; lreg; lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg; lreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := arm_UMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true; IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SMULL_semi (wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wsmul wn wm in
  (lo, hi).

Definition arm_SMULL_instr : instr_desc_t :=
  let mn := SMULL in
  let tin := [:: lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 2; Ea 3 ];
    id_tout := [:: lreg; lreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := arm_SMULL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true; IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SMLAL_semi (dlo dhi wn wm : ty_r) : ty_rr :=
  let (hi, lo) := wsmul wn wm in
  wdadds dhi dlo hi lo.

Definition arm_SMLAL_instr : instr_desc_t :=
  let mn := SMLAL in
  let tin := [:: lreg; lreg; lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg; lreg ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := arm_SMLAL_semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true; IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SMMUL_semi (wn wm : ty_r) : ty_r :=
  wmulhs wn wm.

Definition arm_SMMUL_instr : instr_desc_t :=
  let mn := SMMUL in
  let tin := [:: lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0];
    id_semi_total := arm_SMMUL_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SMMULR_semi (wn wm : ty_r) : ty_r :=
  high_bits reg_size (wsigned wn * wsigned wm + 0x80000000).

Definition arm_SMMULR_instr : instr_desc_t :=
  let mn := SMMULR in
  let tin := [:: lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0];
    id_semi_total := arm_SMMULR_semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition get_hw (hw : halfword) (x : wreg) : u16 :=
  if split_vec 16 x is [:: lo; hi ]
  then if hw is HWT then hi else lo
  else 0%w. (* Never happens. *)

Definition arm_smul_hw_semi (hwn hwm : halfword) (wn wm : wreg) : wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m)%Z in
  wrepr U32 r.

Definition arm_smul_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMUL_hw hwn hwm in
  let tin := [:: lreg; lreg ] in
  let semi := arm_smul_hw_semi hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_smla_hw_semi
  (hwn hwm : halfword) (wn wm acc : wreg) : wreg :=
  let n := get_hw hwn wn in
  let m := get_hw hwm wm in
  let r := (wsigned n * wsigned m + wsigned acc)%Z in
  wrepr U32 r.

Definition arm_smla_hw_instr hwn hwm : instr_desc_t :=
  let mn := SMLA_hw hwn hwm in
  let tin := [:: lreg; lreg; lreg ] in
  let semi := arm_smla_hw_semi hwn hwm in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_smulw_hw_semi (hw : halfword) (wn wm : wreg) : wreg :=
  let m := get_hw hw wm in
  let res := (wsigned wn * wsigned m)%Z in
  let w := wrepr U64 res in
  winit U32 (fun i => wbit_n w (i + 16)).

Definition arm_smulw_hw_instr hw : instr_desc_t :=
  let mn := SMULW_hw hw in
  let tin := [:: lreg; lreg ] in
  let semi := arm_smulw_hw_semi hw in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

(* The carry is left undefined: it depends on the shift. *)
Definition arm_bitwise_semi_t
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : ty_w ws) :
  sem_ltuple_t (snzc ++ [:: lword ws ]) :=
  let res := op (op0 wn) (op1 wm) in
  (:: NF_of_word res, ZF_of_word res, undefined_flag & res).

Definition arm_AND_instr : instr_desc_t :=
  let mn := AND in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_bitwise_semi_t id id wand in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: lreg; lreg ];
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_BFC_semi_t (x : wreg) (lsb width : word U8) : wreg :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then false
    else wbit_n x i
  in
  winit reg_size mk.

Definition arm_BFC_semi_sc := [:: ULt U8 1 32%Z; UGe U8 1%Z 2; UaddLe U8 2 1 32%Z].

Definition arm_BFC_instr : instr_desc_t :=
  let mn := BFC in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lreg; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := arm_BFC_semi_t;
    id_nargs := 3;
    id_args_kinds := ak_reg_imm8_imm8;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := arm_BFC_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_BFI_semi_t (x y : wreg) (lsb width : word U8) : wreg :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then wbit_n y (i - Z.to_nat lsbit)
    else wbit_n x i
  in
  winit reg_size mk.

Definition arm_BFI_semi_sc := [:: ULt U8 2 32%Z; UGe U8 1%Z 3; UaddLe U8 3 2 32%Z].

Definition arm_BFI_instr : instr_desc_t :=
  let mn := BFI in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lreg; lreg; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := arm_BFI_semi_t;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm8_imm8;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := arm_BFI_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_BIC_instr : instr_desc_t :=
  let mn := BIC in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_bitwise_semi_t id wnot wand in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_EOR_instr : instr_desc_t :=
  let mn := EOR in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_bitwise_semi_t id id wxor in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_MVN_semi_t (wn : ty_r) : ty_nzc_r_t :=
  let res := wnot wn in
  (:: NF_of_word res, ZF_of_word res, undefined_flag & res).

Definition arm_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let tin := [:: lreg ] in
  let semi_t := arm_MVN_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi1_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ORR_instr : instr_desc_t :=
  let mn := ORR in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_bitwise_semi_t id id wor in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzc x.

(* At [sham = 0] the three flags are undefined; the values below are then
   filtered out by [id_init]. *)
Definition arm_shift_semi_t
  (op : ty_r -> Z -> ty_r) (op_c : ty_r -> Z -> bool)
  (wn : ty_r) (wsham : word U8) : ty_nzc_r_t :=
  let sham := wunsigned wsham in
  let res := op wn sham in
  (:: NF_of_word res, ZF_of_word res, op_c wn sham & res).

(* The shift amount is the second argument, of type [u8]. *)
Definition arm_sham_ne0 : safety_cond :=
  IOp2 (Oneq (Op_w U8)) (IVar 1) (IOp1 (Oword_of_int U8) (IConst 0)).

Definition arm_shift_init : seq safety_cond :=
  [:: arm_sham_ne0; arm_sham_ne0; arm_sham_ne0; IBool true ].

Definition arm_ASR_C (wn : ty_r) (shift : Z) :=
  if (32 <=? shift)%Z then msb wn
  else wbit_n wn (Z.to_nat (shift - 1)).

Definition arm_ASR_semi_t (wn : ty_r) (wsham : word U8) : ty_nzc_r_t :=
  arm_shift_semi_t (@wsar _) arm_ASR_C wn wsham.

Definition arm_ASR_instr : instr_desc_t :=
  let mn := ASR in
  let tin := [:: lreg; lword U8 ] in
  let semi_t := arm_ASR_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SASR;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := arm_shift_init;
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSL_C (wn : ty_r) (shift: Z) :=
  if (shift <=? 32)%Z then wbit_n wn (32-Z.to_nat shift)
  else false.

Definition arm_LSL_semi_t (wn : ty_r) (wsham : word U8) : ty_nzc_r_t :=
  arm_shift_semi_t (@wshl _) arm_LSL_C wn wsham.

Definition arm_LSL_instr : instr_desc_t :=
  let mn := LSL in
  let tin := [:: lreg; lword U8 ] in
  let semi_t := arm_LSL_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SLSL;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := arm_shift_init;
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_LSR_C (wn : ty_r) (shift : Z) :=
  if (32 <? shift)%Z then false
  else wbit_n wn (Z.to_nat (shift - 1)).

Definition arm_LSR_semi_t (wn : ty_r) (wsham : word U8) : ty_nzc_r_t :=
  arm_shift_semi_t (@wshr _) arm_LSR_C wn wsham.

Definition arm_LSR_instr : instr_desc_t :=
  let mn := LSR in
  let tin := [:: lreg; lword U8 ] in
  let semi_t := arm_LSR_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SLSR;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := arm_shift_init;
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition arm_ROR_C (wn : ty_r) (shift : Z) :=
  let res := wror wn shift in
  msb res.

Definition arm_ROR_semi_t (wn : ty_r) (wsham : word U8) : ty_nzc_r_t :=
  arm_shift_semi_t (@wror _) arm_ROR_C wn wsham.

Definition arm_ROR_instr : instr_desc_t :=
  let mn := ROR in
  let tin := [:: lreg; lword U8 ] in
  let semi_t := arm_ROR_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_reg_reg_reg ++ ak_reg_reg_imm_shift U8 SROR;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := arm_shift_init;
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if set_flags opts
  then x
  else drop_nzc x.

Definition mk_rev_instr mn semi doit :=
  let tin := [:: lreg ] in
  {| id_msb_flag := MSB_MERGE
   ; id_tin := tin
   ; id_in := [:: Ea 1 ]
   ; id_tout := [:: lreg]
   ; id_out := [:: Ea 0 ]
   ; id_semi_total := semi
   ; id_nargs := 2
   ; id_args_kinds := ak_reg_reg
   ; id_eq_size := refl_equal
   ; id_check_dest := refl_equal
   ; id_str_jas := pp_s (string_of_arm_mnemonic mn)
   ; id_safe := [::]
   ; id_err := ErrArith
   ; id_init := [:: IBool true ]
   ; id_pp_asm := pp_arm_op mn opts
   ; id_valid := true
   ; id_doit := doit
   ; id_safe_wf := refl_equal
   ; id_wf := refl_equal
  |}.

Definition arm_REV_semi (w : ty_r) : ty_r :=
  wbswap w.

Definition arm_REV16_semi (w : ty_r) : ty_r :=
  lift1_vec U16 (@wbswap U16) U32 w.

Definition arm_REVSH_semi (w : ty_r) : ty_r :=
  sign_extend U32 (wbswap (zero_extend U16 w)).

Definition arm_REV_instr   := mk_rev_instr REV   arm_REV_semi   DOIT.
Definition arm_REV16_instr := mk_rev_instr REV16 arm_REV16_semi DOIT.
Definition arm_REVSH_instr := mk_rev_instr REVSH arm_REVSH_semi NOT_DOIT. (* Not DIT *)

Definition arm_ADR_semi (wn: ty_r) : ty_r :=
  wn.

Definition arm_ADR_instr : instr_desc_t :=
  let mn := ADR in
  let tin := [:: lreg ] in
  let semi := arm_ADR_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ec 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := NOT_DOIT; (* Not DIT *)
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_MOV_semi_t (wn : ty_r) : ty_nzc_r_t :=
  (:: NF_of_word wn, ZF_of_word wn, undefined_flag & wn).

Definition arm_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let tin := [:: lreg ] in
  let semi_t := arm_MOV_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := snzc_r;
      id_out := ad_nzc ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg ++ ak_reg_imm_ (chk_imm_w16_encoding opts.(set_flags));
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool false; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
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
  let tin := [:: lreg; lword U16 ] in
  let semi := arm_MOVT_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition bit_field_extract_semi_t
  (shr : wreg -> Z -> wreg) (wn : wreg) (widx wwidth : word U8) : wreg :=
  let idx := wunsigned widx in
  let width := wunsigned wwidth in
  shr (wshl wn (32 - width - idx)%Z) (32 - width)%Z.

Definition bit_field_extract_semi_sc := [:: UGe U8 1%Z 2; UaddLe U8 2 1 32%Z].

Definition ak_reg_reg_imm_imm_extr :=
   [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_arm_shift_amout SLSL)) U8 ]; [:: CAimm_sz U8 ] ] ].

Definition arm_UBFX_instr : instr_desc_t :=
  let mn := UBFX in
  let sh := (wshr (sz := reg_size)) in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lreg; lword U8; lword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := bit_field_extract_semi_t sh;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm_imm_extr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := bit_field_extract_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition extend_bits_semi
  (len : Z) (wn : wreg) (wroram : word U8) : wreg :=
  let mask := wrepr reg_size (2 ^ len - 1)%Z in
  let roram := wunsigned wroram in
  wand mask (wror wn roram).

Definition ak_reg_reg_imm8_0_8_16_24 :=
  [:: [:: [:: CAreg]; [:: CAreg]; [:: CAimm (Some CAimmC_arm_0_8_16_24) U8]]].

Definition arm_UXTB_instr : instr_desc_t :=
  let mn := UXTB in
  let tin := [:: lreg; lword U8 ] in
  let semi := extend_bits_semi 8 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_UXTH_instr : instr_desc_t :=
  let mn := UXTH in
  let tin := [:: lreg; lword U8 ] in
  let semi := extend_bits_semi 16 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SBFX_instr : instr_desc_t :=
  let mn := SBFX in
  let sh := (wsar (sz := reg_size)) in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: lreg; lword U8; lword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    (* [0 <= widx < 32] is enforced in args_kinds
       [1 <= wwidth < 33-widx] is enforced by the instruction
       TODO : a safety condition should be added
    *)
    id_semi_total := bit_field_extract_semi_t sh;
    id_nargs := 4;
    id_args_kinds := ak_reg_reg_imm_imm_extr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := bit_field_extract_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition sign_extend_bits_semi
  (len: wsize) (wn: wreg) (wroram: u8) : wreg :=
  sign_extend reg_size (zero_extend len (wror wn (wunsigned wroram))).

Definition arm_SXTB_instr : instr_desc_t :=
  let mn := SXTB in
  let tin := [:: lreg; lword U8 ] in
  let semi := sign_extend_bits_semi U8 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_SXTH_instr : instr_desc_t :=
  let mn := SXTH in
  let tin := [:: lreg; lword U8 ] in
  let semi := sign_extend_bits_semi U16 in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    (* [wroram \in [:: 0; 8; 16; 24 ]] is enforced by args_kinds *)
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_imm8_0_8_16_24;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_CMP_semi_t (wn wm : ty_r) : ty_nzcv_t :=
  let wmnot := wnot wm in
  nzcv_of_aluop_t
      (wn + wmnot + 1)%w
      (wunsigned wn + wunsigned wmnot + 1)%Z
      (wsigned wn + wsigned wmnot + 1)%Z.

Definition arm_CMP_instr : instr_desc_t :=
  let mn := CMP in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_CMP_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
  else x.

Definition arm_TST_semi_t (wn wm : ty_r) : ty_nzc_t :=
  let res := wand wn wm in
  (:: NF_of_word res, ZF_of_word res & false).

Definition arm_TST_instr : instr_desc_t :=
  let mn := TST in
  let tin := [:: lreg; lreg ] in
  let semi_t := arm_TST_semi_t in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzc;
      id_out := ad_nzc;
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_reject_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
  else x.

Definition arm_CMN_instr : instr_desc_t :=
  let mn := CMN in
  let tin := [:: lreg; lreg ] in
  let semi_t := fun wn wm => rtuple_drop5th_t (arm_ADD_semi_t wn wm) in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_reg_reg_or_imm opts chk_imm_accept_shift;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_safe := [::];
      id_err := ErrArith;
      id_init := [:: IBool true; IBool true; IBool true; IBool true ];
      id_pp_asm := pp_arm_op mn opts;
      id_valid := true;
      id_doit := DOIT;
      id_safe_wf := refl_equal;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted sk x (mk_semi2_2_shifted_t sk (id_semi_total x))
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
  let tin := [:: lword ws ] in
  let semi := arm_extend_semi (isSome (wsize_of_sload_mn mn)) reg_size in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_store_instr mn : instr_desc_t :=
  let ws :=
    if wsize_of_store_mn mn is Some ws'
    then ws'
    else U32 (* Never happens. *)
  in
  let tin := [:: lword ws ] in
  let semi := arm_extend_semi false ws in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be a [reg_size] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: lword ws ];
    id_out := [:: Eu 1 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
  |}.

Definition arm_CLZ_instr :=
  let mn := CLZ in
  let tin := [:: lreg ] in
  let semi := fun z => leading_zero z in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_safe := [::];
    id_err := ErrArith;
    id_init := [:: IBool true ];
    id_pp_asm := pp_arm_op mn opts;
    id_valid := true;
    id_doit := DOIT;
    id_safe_wf := refl_equal;
    id_wf := refl_equal;
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
  | SXTB => arm_SXTB_instr
  | SXTH => arm_SXTH_instr
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
