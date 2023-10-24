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
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

Definition arm_op_mov (x y : var_i) : fopn_args :=
  ([:: LLvar x ], Oarm (ARM_op MOV default_opts), [:: Rexpr (Fvar y) ]).

Definition arm_op_movi (x : var_i) (imm : Z) : fopn_args :=
  let e := fconst reg_size imm in
  ([:: LLvar x ], Oarm (ARM_op MOV default_opts), [:: Rexpr e ]).

Definition arm_op_movt (x : var_i) (imm : Z) : fopn_args :=
  let e := fconst U16 imm in
  ([:: LLvar x ], Oarm (ARM_op MOVT default_opts), [:: Rexpr (Fvar x); Rexpr e ]).

Definition arm_op_sub (x y z : var_i) : fopn_args :=
  let f v := Rexpr (Fvar v) in
  ([:: LLvar x ], Oarm (ARM_op SUB default_opts), map f [:: y; z ]).

Definition arm_op_str_off (x y : var_i) (off : Z) : fopn_args :=
  let lv := Store reg_size y (fconst Uptr off) in
  ([:: lv ], Oarm (ARM_op STR default_opts), [:: Rexpr (Fvar x) ]).

Definition arm_op_arith_imm
  (op : arm_mnemonic) (x y : var_i) (imm : Z) : fopn_args :=
  let ey := Rexpr (Fvar y) in
  let eimm := fconst reg_size imm in
  ([:: LLvar x ], Oarm (ARM_op op default_opts), [:: ey; Rexpr eimm ]).

Definition arm_op_addi (x y : var_i) (imm : Z) : fopn_args :=
  arm_op_arith_imm ADD x y imm.

Definition arm_op_subi (x y : var_i) (imm : Z) : fopn_args :=
  arm_op_arith_imm SUB x y imm.

Definition arm_op_align (x y : var_i) (al : wsize) :=
  arm_op_arith_imm BIC x y (wsize_size al - 1).

(* Precondition: [0 <= imm < wbase reg_size]. *)
Definition arm_cmd_load_large_imm (x : var_i) (imm : Z) : seq fopn_args :=
  if is_expandable imm || is_w16_encoding imm
  then [:: arm_op_movi x imm ]
  else
    let '(hbs, lbs) := Z.div_eucl imm (wbase U16) in
    [:: arm_op_movi x lbs; arm_op_movt x hbs ].

(* Return a command that performs an operation with an immediate argument,
   loading it into a register if needed.
   In symbols,
       R[x] := R[y] <+> imm
   Precondition: if [imm] is large, [x <> y].

   We use [is_expandable] but this is an more restrictive than necessary, for
   some mnemonics we could use [is_wXX_encoding]. *)
Definition arm_cmd_large_arith_imm
  (on_reg : var_i -> var_i -> var_i -> fopn_args)
  (on_imm : var_i -> var_i -> Z -> fopn_args)
  (neutral : option Z)
  (x y : var_i)
  (imm : Z) :
  seq fopn_args :=
  let is_mov := if neutral is Some x then (imm =? x)%Z else false in
  if is_mov
  then [:: arm_op_mov x y ]
  else
    if is_expandable imm
    then [:: on_imm x y imm ]
    else arm_cmd_load_large_imm x imm ++ [:: on_reg x y x ].

(* Precondition: if [imm] is large, [x <> y]. *)
Definition arm_cmd_large_subi :=
  arm_cmd_large_arith_imm arm_op_sub arm_op_subi (Some 0%Z).

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
    szp_cmd := fun _ _ _ _ _ _ =>
      Error (stack_zeroization.E.error (compiler_util.pp_s "arm not supported"))
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
