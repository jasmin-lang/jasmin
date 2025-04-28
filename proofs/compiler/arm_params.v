From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  shift_kind.
Require Import
  lea
  linearization
  lowering
  stack_alloc_params
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

Section Section.
Context {atoI : arch_toIdent}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition arm_mov_ofs
  (x : lval) (tag : assgn_tag) (movk : mov_kind) (y : pexpr) (ofs : pexpr) :
  option instr_r :=
  let mk oa :=
    let: (op, args) := oa in
     Some (Copn [:: x ] tag (Oarm (ARM_op op default_opts)) args) in
  match movk with
  | MK_LEA => mk (ADR, [:: if is_zero Uptr ofs then y else add y ofs ])
  | MK_MOV =>
    match x with
    | Lvar x_ =>
      if is_Pload y then
        if is_zero Uptr ofs then mk (LDR, [:: y ]) else None
      else
        match mk_lea Uptr (add y ofs) with
        | None => None
        | Some lea =>
          match lea.(lea_base), lea.(lea_offset) with
          | None, _ => None (* impossible *)
          | Some base, None =>
            if lea.(lea_disp) == 0%Z then mk (MOV, [:: Plvar base ])
            else
              (* This allows to remove constraint in register allocation *)
              if is_arith_small lea.(lea_disp) then mk (ADD, [:: Plvar base; cast_const lea.(lea_disp) ])
              else
                Some (Copn [:: x ] tag (Oasm (ExtOp Oarm_add_large_imm)) [:: Plvar base; cast_const lea.(lea_disp) ])
          | Some base, Some off =>
            if lea.(lea_disp) == 0%Z then
              let%opt scale := Option.map Z.of_nat (shift_of_scale lea.(lea_scale)) in
              if scale == 0%Z then
                (* we have a special case to avoid a trivial shift of 0 *)
                mk (ADD, [:: Plvar base; Plvar off ])
              else
                let opts :=
                  {| set_flags := false; is_conditional := false; has_shift := Some SLSL |}
                in
                Some (Copn [:: x ] tag (Oarm (ARM_op ADD opts)) [:: Plvar base; Plvar off; eword_of_int U8 scale ])
            else None
          end
        end
    | Lmem _ _ _ _ =>
      if is_zero Uptr ofs then mk (STR, [:: y ]) else None
    | _ => None
    end
  end.

Definition arm_immediate (x: var_i) z :=
  Copn [:: Lvar x ] AT_none (Oarm (ARM_op MOV default_opts)) [:: cast_const z ].

Definition arm_swap t (x y z w : var_i) :=
  Copn [:: Lvar x; Lvar y] t (Oasm (ExtOp (Oarm_swap reg_size))) [:: Plvar z; Plvar w].

Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
    sap_immediate := arm_immediate;
    sap_swap := arm_swap;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi  := (mk_var_i (to_var R12)).
Notation vtmp2i := (mk_var_i (to_var LR)).

Definition arm_allocate_stack_frame (rspi : var_i) (tmp: option var_i) (sz : Z) :=
  if tmp is Some aux then
    ARMFopn.smart_subi_tmp rspi aux sz
  else
    [:: ARMFopn.subi rspi rspi sz].

Definition arm_free_stack_frame (rspi : var_i) (tmp : option var_i) (sz : Z) :=
  if tmp is Some aux then
    ARMFopn.smart_addi_tmp rspi aux sz
  else
    [:: ARMFopn.addi rspi rspi sz].

Definition arm_set_up_sp_register
  (rspi : var_i)
  (sf_sz : Z)
  (al : wsize)
  (r : var_i)
  (tmp : var_i) :
  seq fopn_args :=
  let load_imm := ARMFopn.smart_subi tmp rspi sf_sz in
  let i0 := ARMFopn.align tmp tmp al in
  let i1 := ARMFopn.mov r rspi in
  let i2 := ARMFopn.mov rspi tmp in
  load_imm ++ [:: i0; i1; i2 ].

Definition arm_tmp  : Ident.ident := vname (v_var vtmpi).
Definition arm_tmp2 : Ident.ident := vname (v_var vtmp2i).

Definition arm_lmove (xd xs : var_i) :=
  ([:: LLvar xd], Oarm (ARM_op MOV default_opts), [:: Rexpr (Fvar xs)]).

Definition arm_check_ws ws := ws == reg_size.

Definition arm_lstore (xd : var_i) (ofs : Z) (xs : var_i) :=
  let ws := reg_size in
  let mn := STR in
  ([:: Store Aligned ws xd (fconst ws ofs)], Oarm (ARM_op mn default_opts), [:: Rexpr (Fvar xs)]).

Definition arm_lload (xd : var_i) (xs: var_i) (ofs : Z) :=
  let ws := reg_size in
  let mn := LDR in
  ([:: LLvar xd], Oarm (ARM_op mn default_opts), [:: Load Aligned ws xs (fconst ws ofs)]).

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp  := arm_tmp;
    lip_tmp2 := arm_tmp2;
    lip_not_saved_stack := [:: arm_tmp ];
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_set_up_sp_register := arm_set_up_sp_register;
    lip_lmove := arm_lmove;
    lip_check_ws := arm_check_ws;
    lip_lstore  := arm_lstore;
    lip_lload := arm_lload;
    lip_lstores := lstores_imm_dfl arm_tmp2 arm_lstore ARMFopn.smart_addi is_arith_small;
    lip_lloads  := lloads_imm_dfl arm_tmp2 arm_lload  ARMFopn.smart_addi is_arith_small;
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
  | BaseOp (None, ARM_op o opts) =>
    if o \in [:: MOV; LDR; STR; STRH; STRB ] then
      [&& ~~ set_flags opts
        , ~~ is_conditional opts
        & ~~ has_shift opts
      ]
    else false

  | _ =>
      false
  end.

Definition arm_params : architecture_params lowering_options :=
  {|
    ap_sap := arm_saparams;
    ap_lip := arm_liparams;
    ap_plp := false;
    ap_lop := arm_loparams;
    ap_lap := {| lap_lower_address := fun _ p => ok p |};
    ap_agp := arm_agparams;
    ap_szp := arm_szparams;
    ap_shp := arm_shparams;
    ap_is_move_op := arm_is_move_op;
  |}.

End Section.
