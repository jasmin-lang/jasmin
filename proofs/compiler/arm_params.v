From mathcomp Require Import
  all_ssreflect
  all_algebra.

From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr.
Require Import
  linearization
  lowering
  stack_alloc
  stack_zeroization
  slh_lowering.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_params_common
  arm_lowering
  arm_stack_zeroization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition is_load e :=
  if e is Pload _ _ _ then true else false.

Definition arm_mov_ofs
  (x : lval) (tag : assgn_tag) (vpk : vptr_kind) (y : pexpr) (ofs : Z) :
  option instr_r :=
  let mk oa :=
    let: (op, args) := oa in
     Some (Copn [:: x ] tag (Oarm (ARM_op op default_opts)) args) in
  match mk_mov vpk with
  | MK_LEA => mk (ADR, [:: if ofs == Z0 then y else add y (eword_of_int reg_size ofs) ])
  | MK_MOV =>
    match x with
    | Lvar _ =>
      if is_load y then
        if ofs == Z0 then mk (LDR, [:: y]) else None
      else
        if ofs == Z0 then mk (MOV, [:: y]) else mk (ADD, [::y; eword_of_int reg_size ofs ])
    | Lmem _ _ _ =>
      if ofs == Z0 then mk (STR, [:: y]) else None
    | _ => None
    end
  end.

Definition arm_immediate (x: var_i) z :=
  Copn [:: Lvar x ] AT_none (Oarm (ARM_op MOV default_opts)) [:: cast_const z ].

Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
    sap_immediate := arm_immediate;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := (mk_var_i (to_var R12)).

(* TODO_ARM: This assumes 0 <= sz < 4096. *)
Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  arm_op_subi rspi rspi sz.

(* TODO_ARM: This assumes 0 <= sz < 4096. *)
Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  arm_op_addi rspi rspi sz.

(* TODO_ARM: Review. This seems unnecessary. *)
Definition arm_lassign
  (lv : lexpr) (ws : wsize) (e : rexpr) : option _ :=
  let%opt (mn, e') :=
    match lv with
    | LLvar _ =>
        let%opt _ := chk_ws_reg ws in
        match e with
        | Rexpr (Fapp1 (Oword_of_int U32) (Fconst _))
        | Rexpr (Fvar _) => Some (MOV, e)
        | Load _ _ _ => Some (LDR, e)
        | _ => None
        end
    | Store _ _ _ =>
        let%opt mn := store_mn_of_wsize ws in
        Some (mn, e)
    end
  in
  Some ([:: lv ], Oarm (ARM_op mn default_opts), [:: e' ]).

Definition arm_set_up_sp_register
  (rspi : var_i)
  (sf_sz : Z)
  (al : wsize)
  (r : var_i) :
  option (seq fopn_args) :=
  let%opt _ := oassert ((0 <=? sf_sz)%Z && (sf_sz <? wbase reg_size)%Z) in
  let i0 := arm_op_mov r rspi in
  let load_imm := arm_cmd_large_subi vtmpi rspi sf_sz in
  let i1 := arm_op_align vtmpi vtmpi al in
  let i2 := arm_op_mov rspi vtmpi in
  Some (i0 :: load_imm ++ [:: i1; i2 ]).

Definition arm_set_up_sp_stack
  (rspi : var_i) (sf_sz : Z) (al : wsize) (off : Z) : option (seq fopn_args) :=
  let%opt _ := oassert ((0 <=? sf_sz)%Z && (sf_sz <? wbase reg_size)%Z) in
  let load_imm := arm_cmd_large_subi vtmpi rspi sf_sz in
  let i0 := arm_op_align vtmpi vtmpi al in
  let i1 := arm_op_str_off rspi vtmpi off in
  let i2 := arm_op_mov rspi vtmpi in
  Some (load_imm ++ [:: i0; i1; i2 ]).

Definition arm_tmp : Ident.ident := vname (v_var vtmpi).

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp := arm_tmp;
    lip_not_saved_stack := [:: arm_tmp ];
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_set_up_sp_register := arm_set_up_sp_register;
    lip_set_up_sp_stack := arm_set_up_sp_stack;
    lip_lassign := arm_lassign;
  |}.

End LINEARIZATION.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

#[ local ]
Definition arm_fvars_correct
  (fv : fresh_vars)
  {pT : progT}
  (fds : seq fun_decl) :
  bool :=
  fvars_correct (all_fresh_vars fv) (fvars fv) fds.

Definition arm_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i _ _ := lower_i;
    lop_fvars_correct := arm_fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition arm_shparams : sh_params :=
  {|
    shp_lower := fun _ _ _ => None;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition condt_of_rflag (r : rflag) : condt :=
  match r with
  | NF => MI_ct
  | ZF => EQ_ct
  | CF => CS_ct
  | VF => VS_ct
  end.

Definition condt_not (c : condt) : condt :=
  match c with
  | EQ_ct => NE_ct
  | NE_ct => EQ_ct
  | CS_ct => CC_ct
  | CC_ct => CS_ct
  | MI_ct => PL_ct
  | PL_ct => MI_ct
  | VS_ct => VC_ct
  | VC_ct => VS_ct
  | HI_ct => LS_ct
  | LS_ct => HI_ct
  | GE_ct => LT_ct
  | LT_ct => GE_ct
  | GT_ct => LE_ct
  | LE_ct => GT_ct
  end.

Definition condt_and (c0 c1 : condt) : option condt :=
  match c0, c1 with
  | CS_ct, NE_ct => Some HI_ct
  | NE_ct, CS_ct => Some HI_ct
  | NE_ct, GE_ct => Some GT_ct
  | GE_ct, NE_ct => Some GT_ct
  | _, _ => None
  end.

Definition condt_or (c0 c1 : condt) : option condt :=
  match c0, c1 with
  | CC_ct, EQ_ct => Some LS_ct
  | EQ_ct, CC_ct => Some LS_ct
  | EQ_ct, LT_ct => Some LE_ct
  | LT_ct, EQ_ct => Some LE_ct
  | _, _ => None
  end.

Definition is_rflags_GE (r0 r1 : rflag) : bool :=
  match r0, r1 with
  | NF, VF => true
  | VF, NF => true
  | _, _ => false
  end.

Fixpoint assemble_cond ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e ii v in ok (condt_of_rflag r)

  | Fapp1 Onot e =>
      Let c := assemble_cond ii e in ok (condt_not c)

  | Fapp2 Oand e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_and c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (AND)")

  | Fapp2 Oor e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_or c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (OR)")

  | Fapp2 Obeq (Fvar x0) (Fvar x1) =>
      Let r0 := of_var_e ii x0 in
      Let r1 := of_var_e ii x1 in
      if is_rflags_GE r0 r1
      then ok GE_ct
      else Error (E.berror ii e "Invalid condition (EQ).")

  | _ =>
      Error (E.berror ii e "Can't assemble condition.")
  end.

Definition arm_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition arm_szparams : stack_zeroization_params :=
  {|
    szp_cmd := stack_zeroization_cmd;
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition arm_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, ARM_op MOV opts) =>
      [&& ~~ set_flags opts
        , ~~ is_conditional opts
        & ~~ has_shift opts
      ]

  | _ =>
      false
  end.

Definition arm_params : architecture_params lowering_options :=
  {|
    ap_sap := arm_saparams;
    ap_lip := arm_liparams;
    ap_lop := arm_loparams;
    ap_agp := arm_agparams;
    ap_szp := arm_szparams;
    ap_shp := arm_shparams;
    ap_is_move_op := arm_is_move_op;
  |}.

End Section.
