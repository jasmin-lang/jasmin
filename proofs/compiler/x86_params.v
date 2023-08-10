From mathcomp Require Import all_ssreflect all_algebra.
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
  slh_lowering.
Require
  constant_prop
  protect_calls.
Require Import
  arch_decl
  arch_extra
  asm_gen
  label.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* Used to set up stack. *)
Definition x86_op_align (x : var_i) (ws : wsize) (al : wsize) : fopn_args :=
  let f_to_lvar x := LLvar (mk_var_i (to_var x)) in
  let eflags := map f_to_lvar [:: OF; CF; SF; PF; ZF ] in
  let ex := Rexpr (Fvar x) in
  let emask := fconst ws (- wsize_size al) in
  (eflags ++ [:: LLvar x ], Ox86 (AND ws), [:: ex; Rexpr emask ]).

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition lea_ptr x y tag ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr :=
    if mk_mov vpk is MK_LEA
    then
      lea_ptr x y tag ofs
    else
      if ofs == 0%Z
      then mov_ws Uptr x y tag
      else lea_ptr x y tag ofs
  in
  Some addr.

Definition x86_immediate x z :=
  mov_ws Uptr (Lvar x) (cast_const z) AT_none.

Definition x86_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := x86_mov_ofs;
    sap_immediate := x86_immediate;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := (mk_var_i (to_var RAX)).

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Osub (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Oadd (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

(* TODO: consider using VMOVDQA when the address is known to be aligned *)
Definition x86_lassign (x: lexpr) (ws: wsize) (e: rexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_set_up_sp_register
  (rspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) : seq fopn_args :=
  let i0 := x86_lassign (LLvar r) Uptr (Rexpr (Fvar rspi)) in
  let i2 := x86_op_align rspi Uptr al in
  i0 :: rcons (if sf_sz != 0 then [:: x86_allocate_stack_frame rspi sf_sz ] else [::]) i2.

Definition x86_set_up_sp_stack
  (rspi : var_i) (sf_sz : Z) (al : wsize) (off : Z) : seq fopn_args :=
  let vtmpg := Fvar vtmpi in
  let i := x86_lassign (Store Uptr rspi (fconst Uptr off)) Uptr (Rexpr vtmpg) in
  x86_set_up_sp_register rspi sf_sz al vtmpi ++ [:: i ].

Definition x86_liparams : linearization_params :=
  {|
    lip_tmp := vname (v_var vtmpi);
    lip_not_saved_stack := [::];
    lip_allocate_stack_frame := x86_allocate_stack_frame;
    lip_free_stack_frame := x86_free_stack_frame;
    lip_set_up_sp_register :=
      fun rspi sf_sz al r => Some (x86_set_up_sp_register rspi sf_sz al r);
    lip_set_up_sp_stack :=
      fun rspi sf_sz al off => Some (x86_set_up_sp_stack rspi sf_sz al off);
    lip_lassign := fun x ws e => Some (x86_lassign x ws e);
  |}.

End LINEARIZATION.

(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition x86_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i := lower_i;
    lop_fvars_correct := fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition lv_none_flags := nseq 5 (Lnone dummy_var_info sbool).

Definition x86_sh_lower
  (lvs : seq lval)
  (slho : slh_op)
  (es : seq pexpr) :
  option copn_args :=
  let O x := Oasm (ExtOp x) in
  match slho with
  | SLHinit   => Some (lvs, O Ox86SLHinit, es)

  | SLHupdate => Some (Lnone dummy_var_info ty_msf :: lvs, O Ox86SLHupdate, es)

  | SLHmove   => Some (lvs, O (Ox86SLHmove), es)

  | SLHprotect ws =>
      let extra :=
        if (ws <= U64)%CMP
        then lv_none_flags
        else [:: Lnone dummy_var_info (sword ws)]
      in
      Some (extra ++ lvs, O (Ox86SLHprotect ws), es)

  | SLHprotect_ptr _ | SLHprotect_ptr_fail _ => None (* Taken into account by stack alloc *)
  end.

Definition x86_update_after_call (msf : var_i) (msfs : seq var_i) : copn_args :=
  let lvs := Lnone dummy_var_info sreg :: Lvar msf :: map Lvar msfs in
  let es := [:: Pvar (mk_lvar msf) ]
  in
  (lvs, Oasm (ExtOp (Ox86SLHupdate_after_call (size msfs))), es).

Definition x86_shparams : sh_params :=
  {|
    shp_lower := x86_sh_lower;
    shp_update_after_call :=
      fun _ msf msfs => ok (x86_update_after_call msf msfs);
  |}.


(* ------------------------------------------------------------------------ *)
(* Protect calls parameters. *)

Section PROTECT_CALLS.

Import protect_calls.

Section WITH_ERR.

  Context (err : option string -> pp_error_loc).

  Notation rvar := (fun v => Rexpr (Fvar v)) (only parsing).
  Notation rconst := (fun ws imm => Rexpr (fconst ws imm)) (only parsing).

  (* ------------------------------------------------------------------------ *)
  (* TODO: move. *)

  Definition lexpr_flags : seq lexpr :=
    map (fun f => LLvar (mk_var_i (to_var f))) [:: OF; CF; SF; PF; ZF ].

  Definition x86_fop_movi (x : var_i) (imm : Z) : fopn_args :=
    ([:: LLvar x ], Ox86 (MOV reg_size), [:: rconst reg_size imm ]).

  Definition x86_fop_movx (x y : var_i) : fopn_args :=
    ([:: LLvar x ], Ox86 (MOVX reg_size), [:: rvar y ]).

  Definition x86_fop_cmpi (x : var_i) (imm : Z) : fopn_args :=
    let res := [:: rvar x; rconst reg_size imm ] in
    (lexpr_flags, Ox86 (CMP reg_size), res).

  Definition x86_fop_protect_64 (x msf : var_i) : fopn_args :=
    let les := lexpr_flags ++ [:: LLvar x ] in
    (les, Oasm (ExtOp (Ox86SLHprotect U64)), [:: rvar x; rvar msf ]).

  (* TODO: Use [x86_free_stack_frame]. *)
  Definition x86_lcmd_pop (rsp x : var_i) : seq fopn_args :=
    let addr := Load reg_size rsp (fconst reg_size 0) in
    let rsp' :=
      Rexpr
        (Fapp2 (Oadd (Op_w reg_size)) (Fvar (mk_var_i rsp)) (fconst reg_size 8))
    in
    [:: ([:: LLvar x ], Ox86 (MOV reg_size), [:: addr ])
      ; ([:: LLvar rsp ], Ox86 (LEA reg_size), [:: rsp' ])
    ].

  (* TODO: Use [x86_allocate_stack_frame]. *)
  Definition x86_lcmd_pushi (rsp : var_i) (z : Z) : seq fopn_args :=
    let addr := Store reg_size rsp (fconst reg_size 0) in
    let rsp' :=
      Rexpr
        (Fapp2 (Osub (Op_w reg_size)) (Fvar (mk_var_i rsp)) (fconst reg_size 8))
    in
    [:: ([:: LLvar rsp ], Ox86 (LEA reg_size), [:: rsp' ])
      ; ([:: addr ], Ox86 (MOV reg_size), [:: rconst reg_size z ])
    ].

  Fixpoint pexpr_of_fexpr (fe : fexpr) : pexpr :=
    match fe with
    | Fconst z => Pconst z
    | Fvar v => Pvar (mk_lvar v)
    | Fapp1 op1 fe => Papp1 op1 (pexpr_of_fexpr fe)
    | Fapp2 op2 fe0 fe1 => Papp2 op2 (pexpr_of_fexpr fe0) (pexpr_of_fexpr fe1)
    | Fif c fe0 fe1 =>
        Pif
          sbool
          (pexpr_of_fexpr c)
          (pexpr_of_fexpr fe0)
          (pexpr_of_fexpr fe1)
    end.

  Definition fnot (fe : fexpr) : option fexpr :=
    fexpr_of_pexpr (constant_prop.snot (pexpr_of_fexpr fe)).

  Definition r_uncons
    {aT eT} (err : eT) (s : seq aT) : result eT (aT * seq aT) :=
    if s is a :: s' then ok (a, s') else Error err.

  (* ------------------------------------------------------------------------ *)

  Let fcond_eq := Fvar (mk_var_i (to_var ZF)).
  Let fcond_ne := Fapp1 Onot fcond_eq.

  Definition x86_is_update_after_call (op : sopn) : bool :=
    if op is Oasm (ExtOp (Ox86SLHupdate_after_call _)) then true else false.

  (* To update the MSFs after returning from a function call, there are three
     cases:
     1. The callee has only one call site, so it returned via [Lgoto]. No update
     is needed.
     2. The callee has two call sites, so there was only one [CMP]. Therefore we
     update with respect to the flags (EQ for the first call site in the table,
     NE for the second one).
     3. The callee has more call sites, so there are multiple [CMP]s. The first
     call site in the table can update with respect to the flags as in the
     previous case, but all the others need to recompute [CMP r, tag]. All of
     them update with respect to EQ. *)

  Definition update_after_call_cond
    (tag : Z)
    (r : var_i)
    (t : Z)
    (rest : seq (remote_label * Z)) :
    seq fopn_args * fexpr :=
    if tag == t
    then ([::], fcond_eq)
    else
      if rest is [::]
      then ([::], fcond_ne)
      else ([:: x86_fop_cmpi r tag ], fcond_eq).

  Definition x86_lower_update_after_call
    (ret_tbl : seq (remote_label * Z))
    (tag : Z)
    (r : var_i)
    (les : seq lexpr)
    (res : seq rexpr) :
    cexec (seq fopn_args) :=
    match ret_tbl with
    | [::] => Error (err (Some "empty return table"%string))
    | [:: _ ] => ok [::]
    | (_, t) :: _ :: rest =>
        Let: (les0, msfs) :=
          if les is x :: y :: msfs
          then ok ([:: x; y ], msfs)
          else Error (err (Some "invalid update_after_call args"%string))
        in
        let cmd_msf :=
          let '(pre, cond) := update_after_call_cond tag r t rest in
          pre ++ [:: (les0, Oasm (ExtOp Ox86SLHupdate), Rexpr cond :: res)]
        in
        let cmd_msfs :=
          map (fun x => ([:: x ], Oasm (ExtOp Ox86SLHmove), res)) msfs
        in
        ok (cmd_msf ++ cmd_msfs)
    end.

  Definition load_tag (lta : load_tag_args) : var_i * seq linstr_r :=
    let '(ra, c) :=
      match lta with
      | LTAstack rsp r msf =>
          (r, x86_lcmd_pop rsp r ++ [:: x86_fop_protect_64 r msf ])
      | LTAregister ra => (ra, [::])
      | LTAextra_register rx r => (r, [:: x86_fop_movx r rx ])
      end
    in
    (ra, map lir_of_fopn_args c).

  Definition x86_cmd_lcond_remote
    (cond : fexpr)
    (lbl_fresh : label)
    (lbl_remote : remote_label) :
    cexec (seq linstr_r) :=
    Let ncond :=
      o2r (err (Some "could not negate condition"%string)) (fnot cond)
    in
    ok [:: Lcond ncond lbl_fresh
         ; Lgoto lbl_remote
         ; Llabel InternalLabel lbl_fresh
       ].

  Definition add_entry
    (r : var_i)
    (lbl_remote : remote_label)
    (tag : Z)
    (lirs : seq linstr_r)
    (lbl_fresh : positive) :
    cexec (seq linstr_r * positive) :=
    Let cmd_jmp := x86_cmd_lcond_remote fcond_eq lbl_fresh lbl_remote in
    let x := lir_of_fopn_args (x86_fop_cmpi r tag) :: cmd_jmp in
    ok (x ++ lirs, next_lbl lbl_fresh).

  (* The order is reversed because of [foldM].
     It is clearer to reverse here so that in [update_after_call] we have the
     natural ordering. *)
  Definition x86_lower_return
    (lta : load_tag_args)
    (csi : seq (remote_label * Z) * label) :
    cexec (seq linstr_r) :=
    let '(ris, max_lbl) := csi in
    Let: ((rlbl0, _), ris') :=
      r_uncons (err (Some "empty return table"%string)) (rev ris)
    in

    Let pre :=
      if ris' is [::]
      then ok [::]
      else
        let '(r, cmd_load) := load_tag lta in
        Let: (ret_tbl, _) :=
          foldM
            (fun '(rlbl, tag) '(lirs, flbl) => add_entry r rlbl tag lirs flbl)
            ([::], next_lbl max_lbl)
            ris'
        in
        ok (cmd_load ++ ret_tbl)
    in

    ok (pre ++ [:: Lgoto rlbl0 ]).

Definition x86_save_ra
  (err : option string -> pp_error_loc)
  (sral : save_tag_args)
  (tag : Z)
  : cexec (seq fopn_args) :=
  let c :=
    match sral with
    | STAstack rspi => x86_lcmd_pushi rspi tag
    | STAregister r => [:: x86_fop_movi r tag ]
    | STAextra_register rx r =>
        [:: x86_fop_movi r tag
          ; x86_fop_movx rx r
        ]
    end
  in ok c.

  End WITH_ERR.

Definition x86_pcparams : protect_calls_params :=
  {|
    pcp_is_update_after_call := x86_is_update_after_call;
    pcp_lower_update_after_call := x86_lower_update_after_call;
    pcp_lower_return := x86_lower_return;
    pcp_save_ra := x86_save_ra;
  |}.

End PROTECT_CALLS.


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

Definition of_var_e_bool ii (v: var_i) : cexec rflag :=
  match of_var v with
  | Some r => ok r
  | None => Error (asm_gen.E.invalid_flag ii v)
  end.

Fixpoint assemble_cond_r ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e_bool ii v in
      match r with
      | OF => ok O_ct
      | CF => ok B_ct
      | ZF => ok E_ct
      | SF => ok S_ct
      | PF => ok P_ct
      end

  | Fapp1 Onot e =>
      Let c := assemble_cond_r ii e in
      ok (not_condt c)

  | Fapp2 Oor e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      or_condt ii e c1 c2

  | Fapp2 Oand e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      and_condt ii e c1 c2

  | Fapp2 Obeq (Fvar x1) (Fvar x2) =>
      Let r1 := of_var_e_bool ii x1 in
      Let r2 := of_var_e_bool ii x2 in
      if ((r1 == SF) && (r2 == OF)) || ((r1 == OF) && (r2 == SF))
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: fexpr) : cexec condt :=
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
  | BaseOp (None, VMOVDQA _) => true
  | BaseOp (None, VMOVDQU _) => true
  | ExtOp Ox86SLHmove => true
  | _ => false
  end.

(* ------------------------------------------------------------------------ *)

Definition x86_params : architecture_params lowering_options :=
  {|
    ap_sap := x86_saparams;
    ap_lip := x86_liparams;
    ap_lop := x86_loparams;
    ap_agp := x86_agparams;
    ap_shp := x86_shparams;
    ap_pcp := x86_pcparams;
    ap_is_move_op := x86_is_move_op;
  |}.

End Section.
