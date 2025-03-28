From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr.
Require Import
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
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv_lowering
  riscv_params_core
  riscv_params_common
  riscv_stack_zeroization
  riscv_lower_addressing.

Section Section.
Context {atoI : arch_toIdent}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition is_load e :=
  if e is Pload _ _ _ _ then true else false.

Definition riscv_mov_ofs
  (x : lval) (tag : assgn_tag) (movk : mov_kind) (y : pexpr) (ofs : pexpr) :
  option instr_r :=
  let mk oa :=
    let: (op, args) := oa in
     Some (Copn [:: x ] tag (Oriscv op) args) in
  match movk with
  | MK_LEA => mk (LA, [:: if is_zero Uptr ofs then y else add y ofs ])
  | MK_MOV =>
    match x with
    | Lvar x_ =>
      if is_load y then
        if is_zero Uptr ofs then mk (LOAD Signed U32, [:: y]) else None
      else
        if is_zero Uptr ofs then mk (MV, [:: y])
        else
          if is_wconst_of_size Uptr ofs is Some zofs then
            (* This allows to remove constraint in register allocation *)
            if is_arith_small zofs then mk (ADDI, [::y; ofs ])
            else
              (* These checks are not needed for the proof, but it is probably better
                 to fail here than in asm_gen. *)
              if y is Pvar y_ then
                if [&& vtype x_ == sword U32 & vtype y_.(gv) == sword U32] then
                  Some (Copn [::x] tag (Oasm (ExtOp Oriscv_add_large_imm)) [::y; ofs ])
                else None
              else None
          else
            mk (LA, [:: add y ofs])
    | Lmem _ _ _ _ =>
      if is_zero Uptr ofs then mk (STORE U32, [:: y]) else None
    | _ => None
    end
  end.

Definition riscv_immediate (x: var_i) z :=
  Copn [:: Lvar x ] AT_none (Oriscv LI) [:: cast_const z ].

Definition riscv_swap t (x y z w : var_i) :=
  Copn [:: Lvar x; Lvar y] t (Oasm (ExtOp (SWAP reg_size))) [:: Plvar z; Plvar w].

Definition riscv_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := riscv_mov_ofs;
    sap_immediate := riscv_immediate;
    sap_swap := riscv_swap;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi  := (mk_var_i (to_var X28)).
Notation vtmp2i := (mk_var_i (to_var X29)).

Definition riscv_allocate_stack_frame (rspi : var_i) (tmp: option var_i) (sz : Z) :=
  if tmp is Some aux then
    RISCVFopn.smart_subi_tmp rspi aux sz
  else
    [:: RISCVFopn.subi rspi rspi sz].

Definition riscv_free_stack_frame (rspi : var_i) (tmp : option var_i) (sz : Z) :=
  if tmp is Some aux then
    RISCVFopn.smart_addi_tmp rspi aux sz
  else
    [:: RISCVFopn.addi rspi rspi sz].

Definition riscv_set_up_sp_register
  (rspi : var_i)
  (sf_sz : Z)
  (al : wsize)
  (r : var_i)
  (tmp : var_i) :
  seq fopn_args :=
  let i0 := RISCVFopn.mov r rspi in
  let i2 := RISCVFopn.align rspi rspi al in
  i0 :: rcons (if sf_sz != 0%Z then RISCVFopn.smart_subi rspi r sf_sz else [::]) i2.

Definition riscv_tmp  : Ident.ident := vname (v_var vtmpi).
Definition riscv_tmp2 : Ident.ident := vname (v_var vtmp2i).

Definition riscv_lmove (xd xs : var_i) :=
  ([:: LLvar xd], Oriscv MV, [:: Rexpr (Fvar xs)]).

Definition riscv_check_ws ws := ws == reg_size.

Definition riscv_lstore (xd : var_i) (ofs : Z) (xs : var_i) :=
  let ws := reg_size in
  ([:: Store Aligned ws xd (fconst ws ofs)], Oriscv (STORE ws), [:: Rexpr (Fvar xs)]).

Definition riscv_lload (xd : var_i) (xs: var_i) (ofs : Z) :=
  let ws := reg_size in
  ([:: LLvar xd], Oriscv (LOAD Signed ws), [:: Load Aligned ws xs (fconst ws ofs)]).

Definition riscv_liparams : linearization_params :=
  {|
    lip_tmp  := riscv_tmp;
    lip_tmp2 := riscv_tmp2;
    lip_not_saved_stack := [:: riscv_tmp ];
    lip_allocate_stack_frame := riscv_allocate_stack_frame;
    lip_free_stack_frame := riscv_free_stack_frame;
    lip_set_up_sp_register := riscv_set_up_sp_register;
    lip_lmove := riscv_lmove;
    lip_check_ws := riscv_check_ws;
    lip_lstore  := riscv_lstore;
    lip_lload := riscv_lload;
    lip_lstores := lstores_imm_dfl riscv_tmp2 riscv_lstore RISCVFopn.smart_addi is_arith_small;
    lip_lloads  := lloads_imm_dfl riscv_tmp2 riscv_lload  RISCVFopn.smart_addi is_arith_small;
  |}.

End LINEARIZATION.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)
Definition riscv_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i _ _ _ := lower_i;
    lop_fvars_correct := fun _ _ _ => true; (* No fresh variable introduced *)
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition riscv_shparams : sh_params :=
  {|
    shp_lower := fun _ _ _ => None;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition condt_not (c : condt) : condt :=
  let ck :=
    match c.(cond_kind) with
    | EQ => NE
    | NE => EQ
    | GE sg => LT sg
    | LT sg => GE sg
    end
  in
  {|
    cond_kind:= ck;
    cond_fst:= c.(cond_fst);
    cond_snd:= c.(cond_snd);
  |}
.

Definition assemble_cond_arg ii e : cexec (option register) :=
  match e with
  | Fvar x => Let r := of_var_e ii x in ok (Some r)
  | Fapp1 (Oword_of_int U32) (Fconst 0) => ok None
  | _ => Error (E.berror ii e "Can't assemble condition.")
  end.

(* Returns a condition_kind + a boolean describing if the arguments must be
   swapped. *)
Definition assemble_cond_app2 (o : sop2) :=
  match o with
  | Oeq (Op_w U32) => Some (EQ, false)
  | Oneq (Op_w U32) => Some (NE, false)
  | Olt (Cmp_w sg U32) => Some (LT sg, false)
  | Oge (Cmp_w sg U32) => Some (GE sg, false)
  | Ogt (Cmp_w sg U32) => Some (LT sg, true)
  | Ole (Cmp_w sg U32) => Some (GE sg, true)
  | _ => None
  end.

Fixpoint assemble_cond ii (e : fexpr) : cexec condt :=
  match e with
  | Fapp1 Onot e =>
    Let c := assemble_cond ii e in ok (condt_not c)
  | Fapp2 o e0 e1 =>
    Let: (o, swap) :=
      o2r (E.berror ii e "Could not match condition.") (assemble_cond_app2 o)
    in
    Let arg0 := assemble_cond_arg ii e0 in
    Let arg1 := assemble_cond_arg ii e1 in
    let: (arg0, arg1) := if swap then (arg1, arg0) else (arg0, arg1) in
    ok {|
      cond_kind := o;
      cond_fst := arg0;
      cond_snd := arg1;
    |}
  | _ =>
      Error (E.berror ii e "Can't assemble condition.")
  end.

Definition riscv_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition riscv_szparams : stack_zeroization_params :=
  {|
    szp_cmd := stack_zeroization_cmd
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition riscv_laparams : lower_addressing_params :=
  {|
    lap_lower_address := lower_addressing_prog (pT:=progStack)
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
    ap_plp := true;
    ap_lop := riscv_loparams;
    ap_agp := riscv_agparams;
    ap_lap := riscv_laparams;
    ap_szp := riscv_szparams;
    ap_shp := riscv_shparams;
    ap_is_move_op := riscv_is_move_op;
  |}.

End Section.
