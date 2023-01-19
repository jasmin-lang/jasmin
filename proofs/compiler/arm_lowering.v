From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import
  compiler_util
  expr
  lowering
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

Notation lowered_pexpr := (option (arm_op * seq pexpr)) (only parsing).

(* -------------------------------------------------------------------- *)
(* Fresh variables. *)
(* This pass is parameterized by four variable names that will be used to create
   variables for the processor flags. *)

Record fresh_vars :=
  {
    fv_NF : Ident.ident;
    fv_ZF : Ident.ident;
    fv_CF : Ident.ident;
    fv_VF : Ident.ident;
  }.

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
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool).

Notation is_lval_in_memory := (is_lval_in_memory is_var_in_memory).


(* -------------------------------------------------------------------- *)
(* Lowering of conditions. *)

#[ local ]
Definition mk_fv_vari x := {| v_var := x; v_info := dummy_var_info; |}.

#[ local ]
Definition mk_fv_gvar x := {| gv := mk_fv_vari x; gs := Slocal; |}.

Definition lflags_of_mn (mn : arm_mnemonic) : seq lval :=
  let ids :=
    match mn with
    | CMP => [:: fv_NF; fv_ZF; fv_CF; fv_VF ]
    | TST => [:: fv_NF; fv_ZF; fv_CF ]
    | _ => [::]
    end
  in
  map (fun x => Lvar (mk_fv_vari (vbool (x fv)))) ids.

Definition lower_TST (e0 e1 : pexpr) : option (seq pexpr) :=
  match e0, e1 with
  | Papp2 (Oland _) e00 e01, Papp1 (Oword_of_int _) (Pconst 0) =>
      Some [:: e00; e01 ]
  | _, _ =>
      None
  end.

Definition lower_condition_Papp2
  (op : sop2) (e0 e1 : pexpr) : option (arm_mnemonic * pexpr * seq pexpr) :=
  let eNF := Pvar (mk_fv_gvar (fvNF fv)) in
  let eZF := Pvar (mk_fv_gvar (fvZF fv)) in
  let eCF := Pvar (mk_fv_gvar (fvCF fv)) in
  let eVF := Pvar (mk_fv_gvar (fvVF fv)) in
  (* TODO_ARM: CMP and TST take register shifts. *)
  let cmp e := Some (CMP, e, [:: e0; e1 ]) in
  match op with
  | Oeq (Op_w U32) =>
      if lower_TST e0 e1 is Some es then Some (TST, eZF, es) else cmp eZF
  | Oneq (Op_w U32) =>
      cmp (enot eZF)
  | Olt (Cmp_w Signed U32) =>
      cmp (eneq eNF eVF)
  | Olt (Cmp_w Unsigned U32) =>
      cmp (enot eCF)
  | Ole (Cmp_w Signed U32) =>
      cmp (eor eZF (eneq eNF eVF))
  | Ole (Cmp_w Unsigned U32) =>
      cmp (eor (enot eCF) eZF)
  | Ogt (Cmp_w Signed U32) =>
      cmp (eand (enot eZF) (eeq eNF eVF))
  | Ogt (Cmp_w Unsigned U32) =>
      cmp (eand eCF (enot eZF))
  | Oge (Cmp_w Signed U32) =>
      cmp (eeq eNF eVF)
  | Oge (Cmp_w Unsigned U32) =>
      cmp eCF
  | _ =>
      None
  end.

Definition lower_condition_pexpr
  (e : pexpr) : option (seq lval * sopn * seq pexpr * pexpr) :=
  if e is Papp2 op e0 e1
  then
    if lower_condition_Papp2 op e0 e1 is Some (mn, e', es)
    then Some (lflags_of_mn mn, Oarm (ARM_op mn default_opts), es, e')
    else None
  else
    None.

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
    if shift_of_sop2 ws op is Some sh
    then
      if check_shift_amount sh z then Some (v, sh, n) else None
    else
      None
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
  if ws is U32
  then
    let mn := if is_var_in_memory (gv v) then LDR else MOV in
    Some (ARM_op mn default_opts, [:: Pvar v ])
  else
    None.

(* Lower an expression of the form [(ws)[v + e]].
   Precondition:
   - [v] is a register.
   - [e] is one of the following:
     + a register.
     + an immediate. *)
Definition lower_Pload
  (ws ws' : wsize) (v : var_i) (e : pexpr) : lowered_pexpr :=
  if ws is U32
  then Some (ARM_op LDR default_opts, [:: Pload ws' v e ])
  else None.

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

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : lowered_pexpr :=
  if ws is U32
  then
    match op with
    | Oword_of_int U32 =>
        Some (ARM_op MOV default_opts, [:: Papp1 op e ])
    | Osignext U32 ws' =>
        if is_load e
        then
          if sload_mn_of_wsize ws' is Some mn
          then Some (ARM_op mn default_opts, [:: e ])
          else None
        else
          None
    | Ozeroext U32 ws' =>
        if is_load e
        then
          if uload_mn_of_wsize ws' is Some mn
          then Some (ARM_op mn default_opts, [:: e ])
          else None
        else
          None
    | Olnot U32 =>
        Some (arg_shift MVN U32 [:: e ])
    | _ =>
        None
    end
  else
    None.

Definition lower_Papp2_op
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) :
  option (arm_mnemonic * pexpr * pexprs) :=
  if ws is U32
  then
    match op with
    | Oadd (Op_w _) =>
        Some (ADD, e0, [:: e1 ])
    | Omul (Op_w _) =>
        Some (MUL, e0, [:: e1 ])
    | Osub (Op_w _) =>
        Some (SUB, e0, [:: e1 ])
    | Odiv (Cmp_w Signed U32) =>
        Some (SDIV, e0, [:: e1 ])
    | Odiv (Cmp_w Unigned U32) =>
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
    | _ =>
        None
    end
  else
    None.

(* Lower an expression of the form [a <+> b].
   Precondition:
   - [a] is a register.
   - [b] is one of the following:
     + a register.
     + a shifted register.
     + an immediate word. *)
Definition lower_Papp2
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) : lowered_pexpr :=
  if lower_Papp2_op ws op e0 e1 is Some (mn, e0', e1')
  then
    let '(aop, es) := arg_shift mn ws e1' in Some (aop, e0' :: es)
  else
    None.

Definition lower_pexpr_aux (ws : wsize) (e : pexpr) : lowered_pexpr :=
  match e with
  | Pvar v => lower_Pvar ws v
  | Pload ws' v e => lower_Pload ws ws' v e
  | Papp1 op e => lower_Papp1 ws op e
  | Papp2 op a b => lower_Papp2 ws op a b
  | _ => None
  end.

Definition no_pre (ole : lowered_pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  if ole is Some (aop, es) then Some ([::], aop, es) else None.

Definition lower_pexpr (ws : wsize) (e : pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  if e is Pif (sword ws') c e0 e1 then
    if lower_pexpr_aux ws e0 is Some (ARM_op mn opts, es)
    then
      if ws == ws'
      then
        let '(pre, c') := lower_condition c in
        Some (pre, ARM_op mn (set_is_conditional opts), es ++ [:: c'; e1 ])
      else
        None
    else
      None
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
  if store_mn_of_wsize ws is Some mn
  then
    let args :=
      match e with
      | Pvar _ => Some (default_opts, [:: e ])
      | Pif _ c e0 e1 => Some (set_is_conditional default_opts, [:: e0; c; e1 ])
      | _ => None
      end
    in
    if args is Some (opts, es)
    then Some (ARM_op mn opts, es)
    else None
  else
    None.

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn
  (lv : lval) (ty : stype) (e : pexpr) : option (seq instr_r * copn_args) :=
  if ty is sword ws
  then
    let le :=
      if is_lval_in_memory lv
      then no_pre (lower_store ws e)
      else lower_pexpr ws e
    in
    if le is Some (pre, aop, es)
    then Some (pre, ([:: lv ], Oarm aop, es))
    else None
  else
    None.


(* -------------------------------------------------------------------- *)
(* Lowering of architecture-specific operations. *)

Definition lower_add_carry
  (lvs : seq lval) (es : seq pexpr) : option copn_args :=
  match lvs, es with
  | [:: cf; r ], [:: x; y; b ] =>
      let args :=
        match b with
        | Pbool false => Some (ADD, [:: x; y ])
        | Pvar _ => Some (ADC, es)
        | _ => None
        end
      in
      if args is Some (mn, es')
      then
        let opts :=
          {| set_flags := true; is_conditional := false; has_shift := None; |}
        in
        let lnoneb := Lnone dummy_var_info sbool in
        let lvs' := [:: lnoneb; lnoneb; cf; lnoneb; r ] in
        Some (lvs', Oasm (BaseOp (None, ARM_op mn opts)), es')
      else
        None
  | _, _ =>
      None
  end.

(* TODO_ARM: Lower shifts. *)
Definition lower_base_op
  (lvs : seq lval) (aop : arm_op) (es : seq pexpr) : option copn_args :=
  let '(ARM_op mn opts) := aop in
  if mn \in has_shift_mnemonics
  then Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es)
  else None.

Definition lower_copn
  (lvs : seq lval) (op : sopn) (es : seq pexpr) : option copn_args :=
  match op with
  | Oaddcarry U32 => lower_add_carry lvs es
  | Oasm (BaseOp (None, aop)) => lower_base_op lvs aop es
  | _ => None
  end.


(* -------------------------------------------------------------------- *)

Definition lowering_options := unit.

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      let irs :=
        if lower_cassgn lv ty e is Some (pre, (lvs, op, es))
        then pre ++ [:: Copn lvs tag op es ]
        else [:: ir ]
      in
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
