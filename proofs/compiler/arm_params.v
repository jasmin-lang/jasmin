From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  arch_params
  compiler_util
  expr.
Require Import
  clear_stack
  linearization
  lowering
  stack_alloc.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition addi x tag y ofs :=
  let eofs := Papp1 (Oword_of_int reg_size) (Pconst ofs) in
  Copn [:: x ] tag (Oarm (ARM_op ADD default_opts)) [:: y; eofs ].

Definition arm_mov_ofs
  (x : lval) tag (_ : vptr_kind) (y : pexpr) (ofs : Z) : option instr_r :=
  Some (addi x tag y ofs).

Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  let esz := Papp1 (Oword_of_int reg_size) (Pconst sz) in
  ([:: Lvar rspi ], Oarm (ARM_op ADD default_opts), [:: Pvar rspg; esz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  let esz := Papp1 (Oword_of_int reg_size) (Pconst (-sz)) in
  ([:: Lvar rspi ], Oarm (ARM_op ADD default_opts), [:: Pvar rspg; esz ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Papp1 (Oword_of_int reg_size) (Pconst (- wsize_size al)) in
  ([:: Lvar rspi ], Oarm (ARM_op AND default_opts), [:: p0; p1 ]).

(* TODO_ARM: Review. This seems unnecessary. *)
Definition arm_lassign
  (lv : lval) (ws : wsize) (e : pexpr) : option copn_args :=
  let args :=
    match lv with
    | Lvar _ =>
        if ws is U32
        then
          match e with
          | Pvar _ =>
              Some (MOV, e)
          | Pload _ _ _ =>
              Some (LDR, e)
          | Papp1 (Ozeroext U32 ws') e' =>
              if e' is Pload _ _ _
              then
                if uload_mn_of_wsize ws' is Some mn
                then Some (mn, e')
                else None
              else
                None
          | _ =>
              None
          end
        else
          None
    | Lmem _ _ _ =>
        if store_mn_of_wsize ws is Some mn
        then Some (mn, e)
        else None
    | _ =>
        None
    end
  in
  if args is Some (mn, e')
  then Some ([:: lv ], Oarm (ARM_op mn default_opts), [:: e' ])
  else None.

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp := "r12"%string; (* TODO_ARM: Review. *)
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lip_lassign := arm_lassign;
  |}.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

#[ local ]
Definition arm_fvars_correct
  (fv : fresh_vars)
  {eft : eqType}
  {pT : progT eft}
  (fds : seq fun_decl) :
  bool :=
  fvars_correct (all_fresh_vars fv) (fvars fv) fds.

Definition arm_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := fun _ _ => lower_i;
    lop_fvars_correct := arm_fvars_correct;
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

Fixpoint assemble_cond ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v =>
      Let r := of_var_e ii (gv v) in ok (condt_of_rflag r)

  | Papp1 Onot e =>
      Let c := assemble_cond ii e in ok (condt_not c)

  | Papp2 Oand e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_and c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (AND)")

  | Papp2 Oor e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_or c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (OR)")

  | Papp2 Obeq (Pvar x0) (Pvar x1) =>
      Let r0 := of_var_e ii (gv x0) in
      Let r1 := of_var_e ii (gv x1) in
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

(* FIXME: put real values here *)
Definition arm_csparams : clear_stack_params :=
  {|
    cs_max_ws := U32;
    cs_clear_stack_cmd := fun _ _ _ => None
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

Definition arm_params : architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := (fun _ => arm_saparams);
    ap_lip := arm_liparams;
    ap_lop := arm_loparams;
    ap_agp := arm_agparams;
    ap_csp := arm_csparams;
    ap_is_move_op := arm_is_move_op;
  |}.
