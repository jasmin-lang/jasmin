From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import sem_type strings utils word.
Require Export arch_decl.
Require Import arm_decl.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ARM Cortex-M4 instruction set
 *
 * These are the THUMB instructions of ARMv7-M, the instruction set of the M4
 * processor.
 *)

Record arith_opts :=
  { args_size      : wsize
  ; set_flags      : bool
  ; is_conditional : bool
  ; has_shift      : option shift_kind
  }.

Definition arith_opts_beq (ao0 ao1: arith_opts) : bool :=
  (set_flags ao0 == set_flags ao1)
  && (is_conditional ao0 == is_conditional ao1)
  && (has_shift ao0 == has_shift ao1).

Variant arm_op : Type :=
(* Arithmetic *)
| ADC                            (* Add with carry *)
| ADD   of arith_opts            (* Add without carry (register) *)
| ADDI  of arith_opts            (* Add without carry (immediate) *)

| SBC                            (* Subtract with carry *)
| SUB                            (* Subtract without carry *)

| MUL                            (* Multiply *)
| MLA                            (* Multiply and accumulate *)
| MLS                            (* Multiply and subtract *)
| SMLAL                          (* Signed multiply accumulate long *)
| SMULL                          (* Signed multiply long *)
| UMLAL                          (* Unsigned multiply accumulate long *)
| UMULL                          (* Unsigned multiply long *)

| SDIV                           (* Signed integer division *)
| UDIV                           (* Unsigned integer division *)

| SSAT                           (* Signed saturate *)
| USAT                           (* Unsigned saturate *)

| SXTB                           (* Signed extend byte *)
| SXTH                           (* Signed extend halfword *)
| UXTB                           (* Unsigned extend byte *)
| UXTH                           (* Unsigned extend halfword *)

(* Logical *)
| AND of arith_opts              (* Bitwise AND (register) *)
| ANDI of arith_opts             (* Bitwise AND (immediate) *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)
| ORR                            (* Bitwise OR *)

(* Shifts *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)

(* Comparison *)
| CMP                            (* Compare *)
| TST                            (* Test flags *)

(* Other data processing instructions *)
| BIC                            (* Bitwise bit clear *)
| MOV of arith_opts              (* Copy operand to destination *)

(* Loads *)
| LDR   of bool                  (* Load a 32-bit word *)
| LDRH                           (* Load a 16-bit unsigned halfword *)
| LDRSH                          (* Load a 16-bit signed halfword *)
| LDRB                           (* Load a 8-bit unsigned byte *)
| LDRSB                          (* Load a 8-bit signed byte *)
| LDRD                           (* Load two 32-bit words *)
| LDM                            (* Load multiple 32-bit words *)
| LDMIA                          (* Load multiple 32-bit words,
                                    increment base after *)
| LDMDB                          (* Load multiple 32-bit words,
                                    decrement base before *)
| POP                            (* Load multiple 32-bit words from the stack,
                                    decrement sp (defined in terms of LDMIA) *)

(* Stores *)
| STR                            (* Store a 32-bit word *)
| STRH                           (* Store a 16-bit halfword *)
| STRB                           (* Store a 8-bit byte *)
| STRD                           (* Store two 32-bit words *)
| STM                            (* Store multiple 32-bit words *)
| STMIA                          (* Store multiple 32-bit words,
                                    increment base after *)
| STMDB                          (* Store multiple 32-bit words,
                                    decrement base before *)
| PUSH                           (* Store multiple 32-bit words from the stack,
                                    decrement sp (defined in terms of STMDB) *)

(* Other *)
| IT.                            (* Make up to four following instructions
                                    conditional *)

Definition arm_op_dec_eq (op0 op1: arm_op) : {op0 = op1} + {op0 <> op1}.
  by repeat decide equality.
Defined.

Definition arm_op_beq (op0 op1: arm_op) : bool :=
  if arm_op_dec_eq op0 op1 is left _
  then true
  else false.

Lemma arm_op_eq_axiom : Equality.axiom arm_op_beq.
Proof.
  move=> x y.
  apply:(iffP idP);
    last move=> <-;
    rewrite /arm_op_beq;
    by case: arm_op_dec_eq.
Qed.

Definition arm_op_eqMixin := Equality.Mixin arm_op_eq_axiom.
Canonical arm_op_eqType := EqType arm_op arm_op_eqMixin.

Instance eqTC_arm_op : eqTypeC arm_op :=
  { ceqP := arm_op_eq_axiom }.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sregsz := (sword reg_size).
Definition wregsz_ty := sem_tuple [:: sregsz ].

(* Tuple for flag values: (NF, ZF, CF, VF). *)
Notation sflag := (sbool) (only parsing).
Notation sflags := ([:: sflag; sflag; sflag; sflag ]) (only parsing).
Definition nzcv_ty := sem_tuple sflags.

Definition flag_ty := sem_tuple [:: sflag ].
Definition nzcvr_ty := sem_tuple (sflags ++ [:: sregsz ]).

Definition nzcvw_ty sz := sem_tuple (sflags ++ [:: sword sz ]).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions.*)

Definition rflags_ad : seq arg_desc := map F rflags.


(* -------------------------------------------------------------------- *)
(* Common argument kinds. *)

Definition reg_reg_ak := [:: [:: [:: CAreg ]; [:: CAreg ] ] ].
Definition reg_reg_reg_ak := [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ] ].
Definition reg_reg_imm_ak := [:: [:: [:: CAreg ]; [:: CAimmZ  ] ] ].
Definition reg_addr_ak := [:: [:: [:: CAreg ]; [:: CAmem true ] ] ].


(* -------------------------------------------------------------------- *)
(* Common basic lemmas *)

Lemma all_catP A (p: A -> bool) (xs ys: seq A) :
  all p xs
  -> all p ys
  -> all p (xs ++ ys).
Proof.
  move=> Hxs Hys.
  rewrite all_cat.
  by apply/andP.
Qed.

Lemma all2_behead {A B} {p: A -> B -> bool} {xs: seq A} {ys: seq B} :
  all2 p xs ys
  -> all2 p (behead xs) (behead ys).
Proof.
  case: xs; case: ys => //= y ys x xs.
  by move=> /andP [] _.
Qed.

(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (sz: wsize) (w: word sz) := msb w.
Definition ZF_of_word (sz: wsize) (w: word sz) := w == 0%R.

(* Compute the value of the flags for an arithmetic operation.
 * For instance, for <+> a binary operation, this function should be called
 * with
 *   res = w <+> w'
 *   res_unsigned = wunsigned w Z.<+> wunsigned w'
 *   res_signed = wsigned w Z.<+> wsigned w'
 *)
Definition nzcv_of_aluop
  {sz: wsize}
  (res: word sz)     (* Actual result. *)
  (res_unsigned: Z)  (* Result with unsigned interpretation. *)
  (res_signed: Z)    (* Result with signed interpretation. *)
  : nzcv_ty :=
  (:: Some (NF_of_word res)                 (* NF *)
    , Some (ZF_of_word res)                 (* ZF *)
    , Some (wunsigned res != res_unsigned)  (* CF *)
    & Some (wsigned res != res_signed)      (* VF *)
  ).

Definition nzcvw_of_aluop (sz: wsize) (w: word sz) (wu ws: Z) :=
  (merge_tuple (nzcv_of_aluop w wu ws) (w: sem_tuple [:: sword sz ])).


(* -------------------------------------------------------------------- *)
(* Flag setting transformations.
 * Instruction descriptions are defined setting flags. The case where
 * the flags should not be set is considered with `drop_nzcv`.
 *)

Notation behead4 xs := (behead (behead (behead (behead xs)))).

Definition drop_semi_nzcv
  {tin tout} (semi: sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead4 tout))) :=
  behead_tuple (behead_tuple (behead_tuple (behead_tuple semi))).

#[ local ]
Lemma drop_nzcv_eq_size {A B} {p} {xs: seq A} {ys: seq B} :
  p && (size xs == size ys)
  -> p && (size (behead4 xs) == size (behead4 ys)).
Proof.
  move=> /andP [] Hp /eqP Hxy.
  apply/andP.
  by rewrite !size_behead Hxy.
Qed.

#[ local ]
Lemma drop_nzcv_check_dest {A B} {p: A -> B -> bool} {xs: seq A} {ys: seq B} :
  all2 p xs ys
  -> all2 p (behead4 xs) (behead4 ys).
Proof.
  move=> H.
  by do 4 apply: all2_behead.
Qed.

Definition drop_nzcv (idt: instr_desc_t) : instr_desc_t :=
  {| id_msb_flag   := id_msb_flag idt
  ;  id_tin        := id_tin idt
  ;  id_in         := id_in idt
  ;  id_tout       := behead4 (id_tout idt)
  ;  id_out        := behead4 (id_out idt)
  ;  id_semi       := drop_semi_nzcv (id_semi idt)
  ;  id_nargs      := id_nargs idt
  ;  id_args_kinds := id_args_kinds idt
  ;  id_eq_size    := drop_nzcv_eq_size (id_eq_size idt)
  ;  id_tin_narr   := id_tin_narr idt
  ;  id_check_dest := drop_nzcv_check_dest (id_check_dest idt)
  ;  id_str_jas    := id_str_jas idt
  ;  id_wsize      := id_wsize idt
  ;  id_safe       := id_safe idt
  ;  id_pp_asm     := id_pp_asm idt
  |}.
Arguments drop_nzcv : clear implicits.


(* -------------------------------------------------------------------- *)
(* Conditional transformations.
 * Instruction descriptions are defined unconditionally. The following
 * transformation converts an unconditional instruction into a conditional
 * one.
 * The output type is unchanged.
 * The input type is expanded with:
 * - A boolean. It is used to determine if the instruction is executed
 * - The output type. It is used to return the unchanged values if the
 *   instruction is not exectuted
 * The semantics and the rest of the fields are updated accordingly.
 *)

#[ local ]
Lemma mk_cond_eq_size
  {A B} {x y} {xs0 xs1: seq A} {ys0 ys1: seq B} :
  (size xs0 == size ys0) && (size xs1 == size ys1)
  -> (size (xs0 ++ x :: xs1) == size (ys0 ++ y :: ys1))
     && (size xs1 == size ys1).
Proof.
  move=> /andP [] /eqP H0 /eqP H1.
  apply/andP.
  by rewrite 2!size_cat /= H0 H1.
Qed.

#[ local ]
Lemma mk_cond_tin_narr {A} {p: A -> bool} {x} {xs ys: seq A} :
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

Definition mk_semi_cond tin tout (semi: sem_prod tin (exec (sem_tuple tout)))
  : sem_prod (tin ++ sbool :: tout) (exec (sem_tuple tout)) :=
  let f0 res cond : sem_prod tout (exec (sem_tuple tout)) :=
    if cond
    then sem_prod_app (sem_prod_tuple tout) (@Ok _ _)
    else sem_prod_const tout res in
  let f1 : sem_prod tin (sem_prod (sbool :: tout) (exec (sem_tuple tout))) :=
    sem_prod_app semi f0 in
  add_arguments f1.

Definition mk_cond (idt: instr_desc_t) tout_narr : instr_desc_t :=
  {| id_msb_flag   := id_msb_flag idt
  ;  id_tin        := (id_tin idt) ++ sbool :: (id_tout idt)
  ;  id_in         := (id_in idt) ++ E (id_nargs idt) :: (id_out idt)
  ;  id_tout       := id_tout idt
  ;  id_out        := id_out idt
  ;  id_semi       := mk_semi_cond (id_semi idt)
  ;  id_nargs      := (id_nargs idt).+1
  ;  id_args_kinds := map (fun x => x ++ [:: [:: CAcond ] ]) (id_args_kinds idt)
  ;  id_eq_size    := mk_cond_eq_size (id_eq_size idt)
  ;  id_tin_narr   := mk_cond_tin_narr
                        (is_true_true: is_not_sarr sbool)
                        (id_tin_narr idt)
                        tout_narr
  ;  id_check_dest := id_check_dest idt
  ;  id_str_jas    := id_str_jas idt
  ;  id_wsize      := id_wsize idt
  ;  id_safe       := id_safe idt
  ;  id_pp_asm     := id_pp_asm idt
  |}.
Arguments mk_cond : clear implicits.

(* -------------------------------------------------------------------- *)
(* Shift transformations.
 * Instruction descriptions are defined without optionally shifted registers.
 * The following transformation adds a shift argument to an instruction
 * and updates the semantics and the rest of the fields accordingly.
 *)

Definition mk_semi_shifted_reg_reg
  {A} (sk: shift_kind) (semi: sem_prod [:: sregsz; sregsz ] A) :
  sem_prod [:: sregsz; sregsz; sint ] A :=
  fun wn wm shift_amount =>
    semi wn (shift_op sk wm shift_amount).

Definition mk_semi_shifted_reg_imm
  {A} (sk: shift_kind) (semi: sem_prod [:: sregsz; sint ] A) :
  sem_prod [:: sregsz; sint; sint ] A :=
  fun wn imm shift_amount =>
    semi wn (shift_opZ sk imm shift_amount).

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0: seq A} {ys0: seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

Lemma mk_shifted_tin_narr {A} {p: A -> bool} {x} {xs: seq A} :
  p x
  -> all p xs
  -> all p (xs ++ [:: x ]).
Proof.
  move=> Hx Hxs.
  apply: all_catP;
    first done.
  by apply/andP.
Qed.

Definition mk_shifted (sk: shift_kind) (idt: instr_desc_t) semi' :
  instr_desc_t :=
  {| id_msb_flag   := id_msb_flag idt
  ;  id_tin        := (id_tin idt) ++ [:: sint ]
  ;  id_in         := (id_in idt) ++ [:: E (id_nargs idt) ]
  ;  id_tout       := id_tout idt
  ;  id_out        := id_out idt
  ;  id_semi       := semi'
  ;  id_nargs      := (id_nargs idt).+1
  ;  id_args_kinds := map (fun x => x ++ [:: [:: CAimmZ ] ]) (id_args_kinds idt)
  ;  id_eq_size    := mk_shifted_eq_size (id_eq_size idt)
  ;  id_tin_narr   := mk_shifted_tin_narr
                        (is_true_true: is_not_sarr sint)
                        (id_tin_narr idt)
  ;  id_check_dest := id_check_dest idt
  ;  id_str_jas    := id_str_jas idt
  ;  id_wsize      := id_wsize idt
  ;  id_safe       := id_safe idt
  ;  id_pp_asm     := id_pp_asm idt
  |}.
Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Instruction semantics and description. *)

Definition arm_ADD_semi
  (wn wm: wregsz_ty)
  : exec nzcvr_ty :=
  ok (nzcvw_of_aluop
        (wn + wm)
        (wunsigned wn + wunsigned wm)%Z
        (wsigned wn + wsigned wm)%Z).

Definition arm_ADD_instr (opts: arith_opts) : instr_desc_t :=
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sregsz; sregsz ]
       ; id_in         := [:: E 1; E 2 ]
       ; id_tout       := sflags ++ [:: sregsz ]
       ; id_out        := rflags_ad ++ [:: E 0 ]
       ; id_semi       := arm_ADD_semi
       ; id_nargs      := 3
       ; id_args_kinds := reg_reg_reg_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
      |} in
  let x := if has_shift opts is Some sk
           then mk_shifted sk x (mk_semi_shifted_reg_reg sk (id_semi x))
           else x in
  let x := if set_flags opts
           then x
           else drop_nzcv x in
  if is_conditional opts
  then mk_cond x (TODO_ARM : all is_not_sarr (id_tout x))
  (* CHECK: (id_tout x) is opaque here. We could have lemmas
   * stating that the output of set_flags has this property.
   *)
  else x.

Definition arm_ADDI_semi
  (wn: wregsz_ty)
  (imm: Z)
  : exec nzcvr_ty :=
  let wm := wrepr reg_size imm in
  ok (nzcvw_of_aluop
        (wn + wm)
        (wunsigned wn + wunsigned wm)%Z
        (wsigned wn + wsigned wm)%Z).

Definition arm_ADDI_instr (opts: arith_opts) : instr_desc_t :=
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sregsz; sint ]
       ; id_in         := [:: E 1; E 2 ]
       ; id_tout       := sflags ++ [:: sregsz ]
       ; id_out        := rflags_ad ++ [:: E 0 ]
       ; id_semi       := arm_ADDI_semi
       ; id_nargs      := 3
       ; id_args_kinds := reg_reg_imm_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
      |} in
  let x := if set_flags opts
           then x
           else drop_nzcv x in
  if is_conditional opts
  then mk_cond x TODO_ARM (* CHECK *)
  else x.

Definition arm_AND_semi
  (wn wm : wregsz_ty)
  : exec nzcvr_ty :=
  let res := wand wn wm in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , TODO_ARM (* FIXME: C depends on the shift. *)
       , TODO_ARM (* FIXME: V should be unchanged. *)
       & res
     ).

Definition arm_AND_instr (opts: arith_opts) : instr_desc_t :=
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sregsz; sregsz ]
       ; id_in         := [:: E 1; E 2 ]
       ; id_tout       := sflags ++ [:: sregsz ] (* FIXME: Does not set V. *)
       ; id_out        := rflags_ad ++ [:: E 0 ] (* FIXME: Does not set V. *)
       ; id_semi       := arm_AND_semi
       ; id_nargs      := 3
       ; id_args_kinds := reg_reg_reg_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
      |} in
  let x := if has_shift opts is Some sk
           then mk_shifted sk x (mk_semi_shifted_reg_reg sk (id_semi x))
           else x in
  let x := if set_flags opts
           then x
           else drop_nzcv x in
  if is_conditional opts
  then mk_cond x TODO_ARM (* CHECK *)
  else x.

Definition arm_ANDI_semi
  (wn : wregsz_ty)
  (imm : Z)
  : exec nzcvr_ty :=
  let wm := wrepr reg_size imm in
  let res := wand wn wm in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , TODO_ARM (* FIXME: C depends on the value of imm. *)
       , TODO_ARM (* FIXME: V should be unchanged. *)
       & res
     ).

Definition arm_ANDI_instr (opts: arith_opts) : instr_desc_t :=
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sregsz; sint ]
       ; id_in         := [:: E 1; E 2 ]
       ; id_tout       := sflags ++ [:: sregsz ]
       ; id_out        := rflags_ad ++ [:: E 0 ]
       ; id_semi       := arm_ANDI_semi
       ; id_nargs      := 3
       ; id_args_kinds := reg_reg_imm_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
      |} in
  let x := if set_flags opts
           then x
           else drop_nzcv x in
  if is_conditional opts
  then mk_cond x TODO_ARM (* CHECK *)
  else x.

Definition arm_MOV_semi {sz} (wn : word sz) :
  exec (sem_tuple (sflags ++ [:: sword sz ])) :=
  check_size_8_32 sz
  >> ok (nzcvw_of_aluop wn (wunsigned wn) (wsigned wn)).

Definition arm_MOV_instr (opts : arith_opts) : instr_desc_t :=
  let sz := args_size opts in
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sword sz ]
       ; id_in         := [:: E 1 ]
       ; id_tout       := sflags ++ [:: sword sz ]
       ; id_out        := rflags_ad ++ [:: E 0 ]
       ; id_semi       := arm_MOV_semi (sz := sz)
       ; id_nargs      := 2
       ; id_args_kinds := reg_reg_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
    |} in
  let x := if set_flags opts
           then x
           else drop_nzcv x in
  if is_conditional opts
  then mk_cond x TODO_ARM (* CHECK *)
  else x.

Definition arm_LDR_semi (wn : wregsz_ty) : exec wregsz_ty :=
  ok wn.

Definition arm_LDR_instr (is_conditional : bool) : instr_desc_t :=
  let x :=
      {| id_msb_flag   := TODO_ARM
       ; id_tin        := [:: sregsz ]
       ; id_in         := [:: E 1 ]
       ; id_tout       := [:: sregsz ]
       ; id_out        := [:: E 0 ]
       ; id_semi       := arm_LDR_semi
       ; id_nargs      := 2
       ; id_args_kinds := reg_addr_ak
       ; id_eq_size    := refl_equal
       ; id_tin_narr   := refl_equal
       ; id_check_dest := refl_equal
       ; id_str_jas    := TODO_ARM
       ; id_wsize      := TODO_ARM
       ; id_safe       := TODO_ARM
       ; id_pp_asm     := TODO_ARM
    |} in
  if is_conditional
  then mk_cond x TODO_ARM (* CHECK *)
  else x.

(* Description of instructions. *)
Definition arm_instr_desc (o: arm_op) : instr_desc_t :=
  match o with
  | ADD opts  => arm_ADD_instr opts
  | ADDI opts => arm_ADDI_instr opts
  | AND opts  => arm_AND_instr opts
  | ANDI opts => arm_ANDI_instr opts
  | MOV opts  => arm_MOV_instr opts
  | LDR c     => arm_LDR_instr c
  | _         => TODO_ARM
  end.

Definition arm_prim_string : seq (string * prim_constructor arm_op) :=
  TODO_ARM.

Instance arm_op_decl : asm_op_decl arm_op :=
  { instr_desc_op := arm_instr_desc
  ; prim_string   := arm_prim_string
  }.
