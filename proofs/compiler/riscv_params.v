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
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv_lowering
  riscv_params_core
  riscv_params_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition is_load e :=
  if e is Pload _ _ _ then true else false.

Definition riscv_mov_ofs
  (x : lval) (tag : assgn_tag) (vpk : vptr_kind) (y : pexpr) (ofs : Z) :
  option instr_r :=
  let mk oa :=
    let: (op, args) := oa in
     Some (Copn [:: x ] tag (Oriscv op) args) in
  match mk_mov vpk with
  | MK_LEA => mk (LA, [:: if ofs == Z0 then y else add y (eword_of_int reg_size ofs) ])
  | MK_MOV =>
    match x with
    | Lvar x_ =>
      if is_load y then
        if ofs == Z0 then mk (LOAD Signed U32, [:: y]) else None
      else
        if ofs == Z0 then mk (MV, [:: y])
        else
          (* TODO: handle large immediates as in arm *)
          mk (ADD, [::y; eword_of_int reg_size ofs ])
    | Lmem _ _ _ =>
      if ofs == Z0 then mk (STORE U32, [:: y]) else None
    | _ => None
    end
  end.

Definition riscv_immediate (x: var_i) z :=
  Copn [:: Lvar x ] AT_none (Oriscv LI) [:: cast_const z ].

(* Nonesense *)
Definition dummy_instr_r :=
  Cassgn (Lnone dummy_var_info sbool) AT_none sbool (Pbool true).

Definition riscv_swap (t : assgn_tag) (x y z w : var_i) := dummy_instr_r.

Definition riscv_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := riscv_mov_ofs;
    sap_immediate := riscv_immediate;
    sap_swap := riscv_swap;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := (mk_var_i (to_var X28)).

Definition riscv_tmp : Ident.ident := vname (v_var vtmpi).

(* TODO_ARM: Review. This seems unnecessary. *)
Definition riscv_lassign
  (lv : lexpr) (ws : wsize) (e : rexpr) : option _ :=
  let%opt (mn, e') :=
    match lv with
    | LLvar _ =>
        let%opt _ := chk_ws_reg ws in
        match e with
        | Rexpr (Fapp1 (Oword_of_int U32) (Fconst _))
        | Rexpr (Fvar _) => Some (MV, e)
        | Load _ _ _ => Some (LOAD Signed U32, e)
        | _ => None
        end
    | Store _ _ _ =>
        Some (STORE ws, e)
    end
  in
  Some ([:: lv ], Oriscv mn, [:: e' ]).

Definition riscv_set_up_sp_register
  (rspi : var_i)
  (sf_sz : Z)
  (al : wsize)
  (r : var_i) :
  option (seq fopn_args) :=
  let%opt _ := oassert ((0 <=? sf_sz)%Z && (sf_sz <? wbase reg_size)%Z) in
  let i0 := RISCVFopn.mov r rspi in
  let load_imm := RISCVFopn.smart_subi vtmpi rspi sf_sz in
  let i1 := RISCVFopn.align vtmpi vtmpi al in
  let i2 := RISCVFopn.mov rspi vtmpi in
  Some (i0 :: load_imm ++ [:: i1; i2 ]).

Definition riscv_set_up_sp_stack
  (rspi : var_i) (sf_sz : Z) (al : wsize) (off : Z) : option (seq fopn_args) :=
  let%opt _ := oassert ((0 <=? sf_sz)%Z && (sf_sz <? wbase reg_size)%Z) in
  let load_imm := RISCVFopn.smart_subi vtmpi rspi sf_sz in
  let i0 := RISCVFopn.align vtmpi vtmpi al in
  let i1 := RISCVFopn.str rspi vtmpi off in
  let i2 := RISCVFopn.mov rspi vtmpi in
  Some (load_imm ++ [:: i0; i1; i2 ]).


Definition riscv_liparams : linearization_params :=
  {|
    lip_tmp := riscv_tmp;
    lip_not_saved_stack := [:: riscv_tmp ];
    lip_allocate_stack_frame := fun _ _ _ => [::];
    lip_free_stack_frame := fun _ _ _ => [::];
    lip_set_up_sp_register := riscv_set_up_sp_register;
    lip_set_up_sp_stack := riscv_set_up_sp_stack;
    lip_lassign := riscv_lassign;
  |}.

End LINEARIZATION.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)
Definition riscv_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i _ _ _ := lower_i;
    lop_fvars_correct := fun _ _ _ => true;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition riscv_shparams : sh_params :=
  {|
    shp_lower := fun _ _ _ => None;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition riscv_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := fun ii e => Error (E.berror ii e"not implemented");
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition riscv_szparams : stack_zeroization_params :=
  {|
    szp_cmd := fun _ _ _ _ _ _ => Error (stack_zeroization.E.error ( compiler_util.pp_s "not implemented"));
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition riscv_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, MV) =>
     true
  | _ =>
      false
  end.

Definition riscv_params : architecture_params lowering_options :=
  {|
    ap_sap := riscv_saparams;
    ap_lip := riscv_liparams;
    ap_lop := riscv_loparams;
    ap_agp := riscv_agparams;
    ap_szp := riscv_szparams;
    ap_shp := riscv_shparams;
    ap_is_move_op := riscv_is_move_op;
  |}.

End Section.
