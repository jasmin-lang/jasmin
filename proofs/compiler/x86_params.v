From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.

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
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition lea_ptr x y tag ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Section IS_REGX.

Context (is_regx : var -> bool).

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Sglob) => MK_LEA
  | _ => MK_MOV
  end.

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr :=
    if mk_mov vpk is MK_LEA
    then
      lea_ptr x y tag ofs
    else
      if ofs == 0%Z
      then mov_ws is_regx Uptr x y tag
      else lea_ptr x y tag ofs
  in
  Some addr.

End IS_REGX.

Definition x86_saparams is_regx : stack_alloc_params :=
  {|
    sap_mov_ofs := x86_mov_ofs is_regx;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Oadd (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Osub (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_ensure_rsp_alignment (rspi: var_i) (al: wsize) :=
  let to_lvar x := Lvar (VarI (to_var x) xH) in
  let eflags := List.map to_lvar [:: OF ; CF ; SF ; PF ; ZF ] in
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Papp1 (Oword_of_int Uptr) (Pconst (- wsize_size al)) in
  (eflags ++ [:: Lvar rspi ], Ox86 (AND Uptr), [:: p0; p1 ]).

Definition x86_lassign (x: lval) (ws: wsize) (e: pexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_liparams : linearization_params :=
  {|
    lip_tmp := "RAX"%string;
    lip_allocate_stack_frame := x86_allocate_stack_frame;
    lip_free_stack_frame := x86_free_stack_frame;
    lip_ensure_rsp_alignment := x86_ensure_rsp_alignment;
    lip_lassign := x86_lassign;
  |}.

(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition x86_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := lower_i;
    lop_fvars_correct := fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition not_condt (c : condt) :=
  match c with
  | O_ct => NO_ct
  | NO_ct => O_ct
  | B_ct => NB_ct
  | NB_ct => B_ct
  | E_ct => NE_ct
  | NE_ct => E_ct
  | BE_ct => NBE_ct
  | NBE_ct => BE_ct
  | S_ct => NS_ct
  | NS_ct => S_ct
  | P_ct => NP_ct
  | NP_ct => P_ct
  | L_ct => NL_ct
  | NL_ct => L_ct
  | LE_ct => NLE_ct
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt :=
  match c1, c2 with
  | L_ct, E_ct => ok LE_ct
  | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct => ok BE_ct
  | E_ct, B_ct => ok BE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 :=
  match c1, c2 with
  | NB_ct, NE_ct => ok NBE_ct
  | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct => ok NLE_ct
  | NL_ct, NE_ct => ok NLE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Fixpoint assemble_cond_r ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v =>
      Let r := of_var_e ii (gv v) in
      match r with
      | OF => ok O_ct
      | CF => ok B_ct
      | ZF => ok E_ct
      | SF => ok S_ct
      | PF => ok P_ct
      | DF => Error (E.berror ii e "Cannot branch on DF")
      end

  | Papp1 Onot e =>
      Let c := assemble_cond_r ii e in
      ok (not_condt c)

  | Papp2 Oor e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      or_condt ii e c1 c2

  | Papp2 Oand e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      and_condt ii e c1 c2

  | Papp2 Obeq (Pvar x1) (Pvar x2) =>
      Let r1 := of_var_e ii (gv x1) in
      Let r2 := of_var_e ii (gv x2) in
      if ((r1 == SF) && (r2 == OF)) || ((r1 == OF) && (r2 == SF))
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  (* FIXME: We keep this by compatibility but it will be nice to remove it. *)
  | Pif _ (Pvar v1) (Papp1 Onot (Pvar vn2)) (Pvar v2) =>
      Let r1 := of_var_e ii (gv v1) in
      Let rn2 := of_var_e ii (gv vn2) in
      Let r2 := of_var_e ii (gv v2) in
      if [&& r1 == SF, rn2 == OF & r2 == OF]
         || [&& r1 == OF, rn2 == SF & r2 == SF]
      then ok L_ct
      else Error (E.berror ii e "Invalid condition (L)")

  | Pif _ (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar vn2)) =>
      Let r1 := of_var_e ii (gv v1) in
      Let r2 := of_var_e ii (gv v2) in
      Let rn2 := of_var_e ii (gv vn2) in
      if [&& r1 == SF, rn2 == OF & r2 == OF]
         || [&& r1 == OF, rn2 == SF & r2 == SF]
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: pexpr) : cexec condt :=
  assemble_cond_r ii e.

Definition x86_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.


(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition x86_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) => true
  | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

(* ------------------------------------------------------------------------ *)

Definition x86_params : architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := x86_saparams;
    ap_lip := x86_liparams;
    ap_lop := x86_loparams;
    ap_agp := x86_agparams;
    ap_is_move_op := x86_is_move_op;
  |}.
