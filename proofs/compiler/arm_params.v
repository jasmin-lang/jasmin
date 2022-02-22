From mathcomp Require Import all_ssreflect all_algebra.

Require Import
  arch_params
  compiler_util
  expr
  psem
  psem_facts
  sem_one_varmap.
Require Import
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

Definition default_opts : arith_opts :=
  {|
    args_size := reg_size;
    set_flags := false;
    is_conditional := false;
    has_shift := None;
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition addi x tag y ofs :=
  Copn [:: x ] tag (Oarm (ADDI default_opts)) [:: y; Pconst ofs ].

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
  ([:: Lvar rspi ], Oarm (ADDI default_opts), [:: Pvar rspg; Pconst sz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI default_opts), [:: Pvar rspg; Pconst (-sz) ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Pconst (- wsize_size al) in
  ([:: Lvar rspi ], Oarm (ANDI default_opts), [:: p0; p1 ]).

Definition arm_lassign (x : lval) (ws : wsize) (e : pexpr) :=
  let opts :=
    {|
      args_size := ws;
      set_flags := false;
      is_conditional := false;
      has_shift := None;
    |}
  in
  ([:: x ], Oarm (MOV opts), [:: e ]).

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp := "r0"%string;
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lip_lassign := arm_lassign;
  |}.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition arm_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := fun _ _ _ _ => lower_i;
    lop_fvars_correct := arm_fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition assemble_cond ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v =>
      Let r := of_var_e ii (gv v) in
      match r with
      | NF => ok MI_ct
      | ZF => ok EQ_ct
      | CF => ok CS_ct
      | VF => ok VS_ct
      end

  | _ => Error (E.berror ii e "Invalid condition.")
  end.

Definition arm_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.


(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition arm_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, MOV opts) =>
      [&& ~~ set_flags opts
        , ~~ is_conditional opts
        & ~~ has_shift opts
      ]

  | _ =>
      false
  end.

Definition arm_params : architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := arm_saparams;
    ap_lip := arm_liparams;
    ap_lop := arm_loparams;
    ap_agp := arm_agparams;
    ap_is_move_op := arm_is_move_op;
  |}.


