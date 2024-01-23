From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  lowering
  pseudo_operator
  shift_kind.
Require Import
  arch_decl
  arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* -------------------------------------------------------------------- *)
(* Fresh variables. *)
(* This pass is parameterized by four variable names that will be used to create
   variables for the processor flags. *)

Definition fv_NF (fv: fresh_vars) := fv (Ident.name_of_string "__n__") sbool.
Definition fv_ZF (fv: fresh_vars) := fv (Ident.name_of_string "__z__") sbool.
Definition fv_CF (fv: fresh_vars) := fv (Ident.name_of_string "__c__") sbool.
Definition fv_VF (fv: fresh_vars) := fv (Ident.name_of_string "__v__") sbool.

Definition all_fresh_vars (fv : fresh_vars) : seq Ident.ident :=
  [:: fv_NF fv; fv_ZF fv; fv_CF fv; fv_VF fv ].

Definition fvNF (fv : fresh_vars) : var := vbool (fv_NF fv).
Definition fvZF (fv : fresh_vars) : var := vbool (fv_ZF fv).
Definition fvCF (fv : fresh_vars) : var := vbool (fv_CF fv).
Definition fvVF (fv : fresh_vars) : var := vbool (fv_VF fv).

Definition fresh_flags (fv : fresh_vars) : seq var :=
  [:: fvNF fv; fvZF fv; fvCF fv; fvVF fv ].

Definition fvars (fv : fresh_vars) : Sv.t := sv_of_list id (fresh_flags fv).


(* -------------------------------------------------------------------- *)

Section ARM_LOWERING.

Context
  (fv : fresh_vars).

Notation lowered_pexpr := (option (arm_op * seq pexpr)) (only parsing).

Definition chk_ws_reg (ws : wsize) : option unit :=
  oassert (ws == reg_size)%CMP.


(* -------------------------------------------------------------------- *)
(* Lowering of conditions. *)

Definition flags_of_mn (mn : arm_mnemonic) : seq var :=
  let ids :=
    match mn with
    | CMP => [:: fvNF; fvZF; fvCF; fvVF ]
    | TST => [:: fvNF; fvZF; fvCF ]
    | _ => [::]
    end
  in
  map (fun x => x fv) ids.

Definition lflags_of_mn (mn : arm_mnemonic) : seq lval :=
  to_lvals (flags_of_mn mn).

Definition lower_TST (e0 e1 : pexpr) : option (seq pexpr) :=
  match e0, e1 with
  | Papp2 (Oland _) e00 e01, Papp1 (Oword_of_int _) (Pconst 0) =>
      Some [:: e00; e01 ]
  | _, _ =>
      None
  end.

(* TODO_ARM: CMP and TST take register shifts. *)
Definition lower_condition_Papp2
  (op : sop2) (e0 e1 : pexpr) : option (arm_mnemonic * pexpr * seq pexpr) :=
  let%opt (cf, ws) := cf_of_condition op in
  let%opt _ := chk_ws_reg ws in
  let cmp := (CMP, pexpr_of_cf cf (fresh_flags fv), [:: e0; e1 ]) in
  match op with
  | Oeq (Op_w _) =>
      let eZF := Pvar (mk_lvar (mk_var_i (fvZF fv))) in
      Some (if lower_TST e0 e1 is Some es then (TST, eZF, es) else cmp)
  | Oneq (Op_w _)
  | Olt (Cmp_w _ _)
  | Ole (Cmp_w _ _)
  | Ogt (Cmp_w _ _)
  | Oge (Cmp_w _ _)
      => Some cmp
  | _ => None
  end.

Definition lower_condition_pexpr
  (e : pexpr) : option (seq lval * sopn * seq pexpr * pexpr) :=
  let%opt (op, e0, e1) := is_Papp2 e in
  let%opt (mn, e', es) := lower_condition_Papp2 op e0 e1 in
  Some (lflags_of_mn mn, Oarm (ARM_op mn default_opts), es, e').

Definition lower_condition (e : pexpr) : seq instr_r * pexpr :=
  if lower_condition_pexpr e is Some (lvs, op, es, c)
  then ([:: Copn lvs AT_none op es ], c)
  else ([::], e).


(* -------------------------------------------------------------------- *)
(* Lowering of assignments. *)

Definition get_arg_shift
  (ws : wsize) (e : pexprs) : option (pexpr * shift_kind * pexpr) :=
  if e is
    [:: Papp2 op ((Pvar _) as v) ((Papp1 (Oword_of_int U8) (Pconst z)) as n) ]
  then
    let%opt sh := shift_of_sop2 ws op in
    let%opt _ := oassert (check_shift_amount sh z) in
    Some (v, sh, n)
  else
    None.

Definition arg_shift
  (mn : arm_mnemonic) (ws : wsize) (e : pexprs) : arm_op * seq pexpr :=
  let '(osh, es) :=
    if mn \in has_shift_mnemonics
    then
      if get_arg_shift ws e is Some (ebase, sh, esham)
      then (Some sh, [:: ebase; esham ])
      else (None, e)
    else
      (None, e)
  in
  let opts :=
    {| set_flags := false; is_conditional := false; has_shift := osh; |}
  in
  (ARM_op mn opts, es).

(* Lower an expression of the form [v].
   Precondition:
   - [v] is a one of the following:
     + a register.
     + a stack variable. *)
Definition lower_Pvar (ws : wsize) (v : gvar) : lowered_pexpr :=
  let%opt _ := chk_ws_reg ws in
  let mn := if is_var_in_memory (gv v) then LDR else MOV in
  Some (ARM_op mn default_opts, [:: Pvar v ]).

(* Lower an expression of the form [(ws)[v + e]] or [tab[ws e]]. *)
Definition lower_load (ws: wsize) (e: pexpr) : lowered_pexpr :=
  let%opt _ := chk_ws_reg ws in
  Some (ARM_op LDR default_opts, [:: e ]).

Definition is_load (e: pexpr) : bool :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _
  | Psub _ _ _ _ _
  | Papp1 _ _ | Papp2 _ _ _ | PappN _ _ | Pif _ _ _ _
    => false
  | Pvar {| gs := Sglob |}
  | Pget _ _ _ _
  | Pload _ _ _
    => true
  | Pvar {| gs := Slocal ; gv := x |}
    => is_var_in_memory x
  end.

Definition Z_mod_lnot (z : Z) (ws : wsize) : Z :=
  let m := wbase ws in
  (Z.lnot (z mod m) mod m)%Z.

(* If the expression is an integer, we first check that the immediate is either
   a byte or an expandable pattern. If not, we try to use the W-encoding
   (16-bit immediate and we can't set flags). Otherwise, we try to use [MVN]. *)
Definition mov_imm_mnemonic (e : pexpr) : option (arm_mnemonic * pexpr) :=
  if is_const e is Some z
  then
    if is_expandable_or_shift z || is_w16_encoding z then
      Some (MOV, e)
    else
      let nz := Z_mod_lnot z reg_size in
      let%opt _ := oassert (is_expandable_or_shift nz) in
      Some (MVN, Pconst nz)
  else Some (MOV, e).

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : lowered_pexpr :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oword_of_int ws' =>
      let%opt _ := oassert (U32 <= ws')%CMP in
      let%opt (mn, e') := mov_imm_mnemonic e in
      Some (ARM_op mn default_opts, [:: Papp1 (Oword_of_int U32) e' ])
  | Osignext U32 ws' =>
      let%opt _ := oassert (is_load e) in
      let%opt mn := sload_mn_of_wsize ws' in
      Some (ARM_op mn default_opts, [:: e ])
  | Ozeroext U32 ws' =>
      let%opt _ := oassert (is_load e) in
      let%opt mn := uload_mn_of_wsize ws' in
      Some (ARM_op mn default_opts, [:: e ])
  | Olnot U32 =>
      Some (arg_shift MVN U32 [:: e ])
  | Oneg (Op_w U32) =>
      Some (ARM_op RSB default_opts, [:: e; wconst (wrepr U32 0) ])
  | _ =>
      None
  end.

Definition is_mul (e: pexpr) : option (pexpr * pexpr) :=
  if e is Papp2 (Omul (Op_w U32)) x y then Some (x, y) else None.

Definition is_rsb (ws : wsize) (e0 e1: pexpr) :=
  match get_arg_shift ws [:: e0 ], get_arg_shift ws [:: e1 ], is_wconst ws e0 with
  | Some _, None, _
  | None, None, Some _ => true
  | _, _, _ => false
  end.

Definition lower_Papp2_op
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) :
  option (arm_mnemonic * pexpr * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oadd (Op_w _) =>
      if is_mul e0 is Some (x, y)
      then Some (MLA, x, [:: y; e1 ])
      else if is_mul e1 is Some (x, y)
      then Some (MLA, x, [:: y; e0 ])
      else
      Some (ADD, e0, [:: e1 ])
  | Omul (Op_w _) =>
      Some (MUL, e0, [:: e1 ])
  | Osub (Op_w _) =>
      if is_mul e1 is Some (x, y)
      then Some (MLS, x, [:: y; e0 ])
      else
      if is_rsb ws e0 e1
      then Some (RSB, e1, [:: e0])
      else
        Some (SUB, e0, [:: e1 ])
  | Odiv (Cmp_w Signed U32) =>
      Some (SDIV, e0, [:: e1 ])
  | Odiv (Cmp_w Unsigned U32) =>
      Some (UDIV, e0, [:: e1 ])
  | Oland _ =>
      Some (AND, e0, [:: e1 ])
  | Olor _ =>
      Some (ORR, e0, [:: e1 ])
  | Olxor _ =>
      Some (EOR, e0, [:: e1 ])
  | Olsr U32 =>
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (LSR, e0, [:: e1 ])
  | Olsl (Op_w U32) =>
      Some (LSL, e0, [:: e1 ])
  | Oasr (Op_w U32) =>
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (ASR, e0, [:: e1 ])
  | Oror U32 =>
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: e1 ])
  | Orol U32 =>
      let%opt c := is_wconst U8 e1 in
      if c == 0%R then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: wconst (32 - c) ])
  | _ =>
      None
  end.

(* Lower an expression of the form [a <+> b].
   Precondition:
   - [a] is a register.
   - [b] is one of the following:
     + a register.
     + a shifted register.
     + an immediate word. *)
Definition lower_Papp2
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) : lowered_pexpr :=
  let%opt (mn, e0', e1') := lower_Papp2_op ws op e0 e1 in
  let '(aop, es) := arg_shift mn ws e1' in
  Some (aop, e0' :: es).

Definition lower_pexpr_aux (ws : wsize) (e : pexpr) : lowered_pexpr :=
  match e with
  | Pvar v => lower_Pvar ws v
  | Pget _ _ _ _
  | Pload _ _ _=> lower_load ws e
  | Papp1 op e => lower_Papp1 ws op e
  | Papp2 op a b => lower_Papp2 ws op a b
  | _ => None
  end.

Definition no_pre (ole : lowered_pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  let%opt (aop, es) := ole in Some ([::], aop, es).

Definition lower_pexpr (ws : wsize) (e : pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  if e is Pif (sword ws') c e0 e1 then
    let%opt _ := oassert (ws == ws')%CMP in
    let%opt (ARM_op mn opts, es) := lower_pexpr_aux ws e0 in
    let '(pre, c') := lower_condition c in
    Some (pre, ARM_op mn (set_is_conditional opts), es ++ [:: c'; e1 ])
  else
    no_pre (lower_pexpr_aux ws e).

(* Lower an assignment to memory.
   Precondition:
   - [lv] must be one of the following:
     + a variable in memory.
     + a memory location.
   - [e] must be one of the following:
     + a register.
     + an if expression. *)
Definition lower_store (ws : wsize) (e : pexpr) : option (arm_op * seq pexpr) :=
  let%opt mn := store_mn_of_wsize ws in
  let%opt (opts, es) :=
    match e with
    | Pvar _ => Some (default_opts, [:: e ])
    | Pif _ c e0 e1 => Some (set_is_conditional default_opts, [:: e0; c; e1 ])
    | _ => None
    end
  in
  Some (ARM_op mn opts, es).

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn_word
  (lv : lval) (ws : wsize) (e : pexpr) : option (seq instr_r * copn_args) :=
  let%opt (pre, aop, es) :=
    if is_lval_in_memory lv
    then no_pre (lower_store ws e)
    else lower_pexpr ws e
  in
  Some (pre, ([:: lv ], Oarm aop, es)).

Definition lower_cassgn_bool (lv : lval) (tag: assgn_tag) (e : pexpr) : option (seq instr_r) :=
  let%opt (lvs, op, es, c) := lower_condition_pexpr e in
  Some [:: Copn lvs tag op es; Cassgn lv AT_inline sbool c ].

(* -------------------------------------------------------------------- *)
(* Lowering of architecture-specific operations. *)

Definition lower_add_carry
  (lvs : seq lval) (es : seq pexpr) : option copn_args :=
  match lvs, es with
  | [:: cf; r ], [:: x; y; b ] =>
      let%opt (mn, es') :=
        match b with
        | Pbool false => Some (ADD, [:: x; y ])
        | Pvar _ => Some (ADC, es)
        | _ => None
        end
      in
      let opts :=
        {| set_flags := true; is_conditional := false; has_shift := None; |}
      in
      let lnoneb := Lnone dummy_var_info sbool in
      let lvs' := [:: lnoneb; lnoneb; cf; lnoneb; r ] in
      Some (lvs', Oasm (BaseOp (None, ARM_op mn opts)), es')
  | _, _ =>
      None
  end.

Definition lower_mulu (lvs : seq lval) (es : seq pexpr) : option copn_args :=
  Some (lvs, Oasm (BaseOp (None, ARM_op UMULL default_opts)), es).

Definition with_shift opts sh :=
  {| set_flags := set_flags opts; is_conditional := is_conditional opts; has_shift := Some sh |}.

Definition lower_base_op
  (lvs : seq lval) (aop : arm_op) (es : seq pexpr) : option copn_args :=
  let: ARM_op mn opts := aop in
  if has_shift opts != None
  then
    let%opt _ := oassert (mn \in has_shift_mnemonics) in
    Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es)
  else
    if MVN == mn
    then
      match es with
      | x :: rest =>
          if get_arg_shift U32 [:: x ] is Some (ebase, sh, esham)
          then Some (lvs, Oasm (BaseOp (None, ARM_op mn (with_shift opts sh))), ebase :: esham :: rest)
          else Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es)
      | _ => None end
    else if mn \in [:: ADD; SUB; RSB; AND; BIC; EOR; ORR; CMP; TST ]
    then
      match es with
      | x :: y :: rest =>
          if get_arg_shift U32 [:: y ] is Some (ebase, sh, esham)
          then Some (lvs, Oasm (BaseOp (None, ARM_op mn (with_shift opts sh))), x :: ebase :: esham :: rest)
          else Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es)
      | _ => None end
    else if ADC == mn
    then
      match es with
      | x :: y :: z :: rest =>
          if get_arg_shift U32 [:: y ] is Some (ebase, sh, esham)
          then Some (lvs, Oasm (BaseOp (None, ARM_op mn (with_shift opts sh))), x :: ebase :: z :: esham :: rest)
          else Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es)
      | _ => None end
    else None.

Definition lower_swap ty lvs es : option copn_args := 
  match ty with
  | sword sz => 
    if (sz <= U32)%CMP then 
      Some (lvs, Oasm (ExtOp (Oarm_swap sz)), es)
    else None
  | sarr _ => 
      Some (lvs, Opseudo_op (Oswap ty), es)
  | _ => None
  end.

Definition lower_pseudo_operator
  (lvs : seq lval) (op : pseudo_operator) (es : seq pexpr) : option copn_args :=
  match op with
  | Oaddcarry U32 => lower_add_carry lvs es
  | Omulu U32 => lower_mulu lvs es
  | Oswap ty => lower_swap ty lvs es
  | _ => None
  end.

Definition lower_copn
  (lvs : seq lval) (op : sopn) (es : seq pexpr) : option copn_args :=
  match op with
  | Opseudo_op pop => lower_pseudo_operator lvs pop es
  | Oasm (BaseOp (None, aop)) => lower_base_op lvs aop es
  | _ => None
  end.

(* -------------------------------------------------------------------- *)

Definition lowering_options := unit.

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      let oirs :=
        match ty with
        | sword ws =>
            let%opt (pre, (lvs, op, es)) := lower_cassgn_word lv ws e in
            Some (pre ++ [:: Copn lvs tag op es ])
        | sbool => lower_cassgn_bool lv tag e
        | _ => None
        end
      in
      let irs := if oirs is Some irs then irs else [:: ir ] in
      map (MkI ii) irs

  | Copn lvs tag op es =>
      let ir' :=
        if lower_copn lvs op es is Some (lvs', op', es')
        then Copn lvs' tag op' es'
        else ir
      in
      [:: MkI ii ir' ]

  | Cif e c1 c2  =>
      let '(pre, e') := lower_condition e in
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])

  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e c1 =>
      let '(pre, e') := lower_condition e in
      let c0' := conc_map lower_i c0 in
      let c1' := conc_map lower_i c1 in
      [:: MkI ii (Cwhile a (c0' ++ map (MkI ii) pre) e' c1') ]

  | _ =>
      [:: i ]
  end.

End ARM_LOWERING.

End Section.
