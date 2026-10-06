(* Lowering pass for ARMv8-A (AArch64): turn source-level operations into
   architecture-specific operations.

   Ported from the ARMv7-M lowering pass. The main differences follow from
   A64 having no conditional execution: word-sized conditional expressions
   are lowered to CSEL, and there are no conditional stores or conditional
   immediate loads. Word operations are lowered at both register sizes:
   64-bit (X form) and 32-bit (W form). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
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
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a_params_core.

Section Section.
Context {atoI : arch_toIdent}.

(* -------------------------------------------------------------------- *)
(* Fresh variables. *)
(* This pass is parameterized by four variable names that will be used to
   create variables for the processor flags. *)

Definition fv_NF (fv : fresh_vars) := fv "__n__"%string abool.
Definition fv_ZF (fv : fresh_vars) := fv "__z__"%string abool.
Definition fv_CF (fv : fresh_vars) := fv "__c__"%string abool.
Definition fv_VF (fv : fresh_vars) := fv "__v__"%string abool.

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

Section ARMV8A_LOWERING.

Context
  (fv : fresh_vars).

Definition low_expr : Type := option (sopn * seq pexpr).
Definition le_skip : low_expr := None.
Definition le_issue_sopn op es : low_expr := Some (op, es).
Definition le_issue_extra op := le_issue_sopn (Oasm (ExtOp op)).
Definition le_issue_aop aop := le_issue_sopn (Oasm (BaseOp (None, aop))).
Definition le_issue_opts mn opts := le_issue_aop (ARMv8A_op mn opts).
Definition le_issue mn ws := le_issue_opts mn (opts_at ws).

Definition no_pre (ole : low_expr) : option (seq instr_r * sopn * seq pexpr) :=
  let%opt (aop, es) := ole in Some ([::], aop, es).

(* Word operations are lowered at both the X (64-bit) and W (32-bit)
   register sizes. *)
Definition chk_ws_reg (ws : wsize) : option unit :=
  oassert ((ws == U64) || (ws == U32))%CMP.


(* -------------------------------------------------------------------- *)
(* Lowering of conditions. *)

Definition flags_of_mn (mn : armv8a_mnemonic) : seq var :=
  let ids :=
    match mn with
    | CMP => [:: fvNF; fvZF; fvCF; fvVF ]
    | TST => [:: fvNF; fvZF; fvCF; fvVF ]
    | _ => [::]
    end
  in
  map (fun x => x fv) ids.

Definition lflags_of_mn (vi : var_info) (mn : armv8a_mnemonic) : seq lval :=
  [seq Lvar {| v_var := x; v_info := vi; |} | x <- flags_of_mn mn ].

Definition lower_TST (e0 e1 : pexpr) : option (seq pexpr) :=
  match e0, e1 with
  | Papp2 (Oland _) e00 e01, Papp1 (Oword_of_int _) (Pconst 0) =>
      Some [:: e00; e01 ]
  | _, _ =>
      None
  end.

Definition lower_condition_Papp2
  (vi : var_info)
  (op : sop2)
  (e0 e1 : pexpr) :
  option (armv8a_mnemonic * wsize * pexpr * seq pexpr) :=
  let%opt (cf, ws) := cf_of_condition op in
  let%opt _ := chk_ws_reg ws in
  let cmp := (CMP, ws, pexpr_of_cf cf vi (fresh_flags fv), [:: e0; e1 ]) in
  match op with
  | Oeq (Op_w _) =>
      let zf_var := {| v_var := fvZF fv; v_info := vi |} in
      let eZF := Pvar (mk_lvar zf_var) in
      Some (if lower_TST e0 e1 is Some es then (TST, ws, eZF, es) else cmp)
  | Oneq (Op_w _)
  | Olt (Cmp_w _ _)
  | Ole (Cmp_w _ _)
  | Ogt (Cmp_w _ _)
  | Oge (Cmp_w _ _)
      => Some cmp
  | _ => None
  end.

Definition lower_condition_pexpr
  (vi : var_info) (e : pexpr) : option (seq lval * sopn * seq pexpr * pexpr) :=
  let%opt (op, e0, e1) := is_Papp2 e in
  let%opt (mn, ws, e', es) := lower_condition_Papp2 vi op e0 e1 in
  Some (lflags_of_mn vi mn, Oarmv8a (ARMv8A_op mn (opts_at ws)), es, e').

Definition lower_condition (vi : var_info) (e : pexpr) : seq instr_r * pexpr :=
  if lower_condition_pexpr vi e is Some (lvs, op, es, c)
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
    let%opt _ := oassert (check_shift_amount ws z) in
    Some (v, sh, n)
  else
    None.

Definition arg_shift
  (mn : armv8a_mnemonic) (ws : wsize) (e : pexprs) : armv8a_asm_op * seq pexpr :=
  let '(osh, es) :=
    if mn \in has_shift_mnemonics
    then
      if get_arg_shift ws e is Some (ebase, sh, esham)
      then
        if shift_allowed mn sh
        then (Some sh, [:: ebase; esham ])
        else (None, e)
      else (None, e)
    else
      (None, e)
  in
  let opts := {| has_shift := osh; opts_size := ws; |} in
  (ARMv8A_op mn opts, es).

(* Lower an expression of the form [v].
   Precondition:
   - [v] is a one of the following:
     + a register.
     + a stack variable. *)
Definition lower_Pvar (ws : wsize) (v : gvar) : low_expr :=
  let%opt _ := chk_ws_reg ws in
  let mn := if is_var_in_memory (gv v) then LDR else MOV in
  le_issue mn ws [:: Pvar v ].

(* Lower an expression of the form [(ws)[v + e]] or [tab[ws e]]. *)
Definition lower_load (ws : wsize) (e : pexpr) : low_expr :=
  let%opt _ := chk_ws_reg ws in
  le_issue LDR ws [:: e ].

Definition mov_imm_op (ws : wsize) (e : pexpr) : sopn :=
  if isSome (is_const e)
  then Oasm (ExtOp (Oarmv8a_smart_li ws))
  else Oarmv8a (ARMv8A_op MOV (opts_at ws)).

(* Narrow zero- and sign-extending loads. *)
Definition uload_mn (ws ws' : wsize) : option armv8a_mnemonic :=
  match ws' with
  | U8 => Some LDRB
  | U16 => Some LDRH
  | _ => None
  end.

Definition sload_mn (ws ws' : wsize) : option armv8a_mnemonic :=
  match ws' with
  | U8 => Some LDRSB
  | U16 => Some LDRSH
  | U32 => if ws == U64 then Some LDRSW else None
  | _ => None
  end.

(* Register-to-register extensions. *)
Definition sext_mn (ws ws' : wsize) : option armv8a_mnemonic :=
  match ws' with
  | U8 => Some SXTB
  | U16 => Some SXTH
  | U32 => if ws == U64 then Some SXTW else None
  | _ => None
  end.

Definition uext_mn (ws ws' : wsize) : option armv8a_mnemonic :=
  match ws' with
  | U8 => Some UXTB
  | U16 => Some UXTH
  | U32 => if ws == U64 then Some UXTW else None
  | _ => None
  end.

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : low_expr :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oword_of_int ws' =>
      let%opt _ := oassert (ws <= ws')%CMP in
      let op := mov_imm_op ws e in
      le_issue_sopn op [:: Papp1 (Oword_of_int ws) e ]
  | Osignext ws0 ws' =>
      let%opt _ := oassert (ws0 == ws) in
      let%opt _ := oassert (ws' < ws)%CMP in
      if is_load e
      then
        let%opt mn := sload_mn ws ws' in
        le_issue mn ws [:: e ]
      else
        let%opt mn := sext_mn ws ws' in
        le_issue mn ws [:: e ]
  | Ozeroext ws0 ws' =>
      let%opt _ := oassert (ws0 == ws) in
      let%opt _ := oassert (ws' < ws)%CMP in
      if is_load e
      then
        let%opt mn := uload_mn ws ws' in
        le_issue mn ws [:: e ]
      else
        let%opt mn := uext_mn ws ws' in
        le_issue mn ws [:: e ]
  | Olnot ws0 =>
      let%opt _ := oassert (ws0 == ws) in
      let (op, es) := arg_shift MVN ws [:: e ] in
      le_issue_aop op es
  | Oneg (Op_w ws0) =>
      let%opt _ := oassert (ws0 == ws) in
      let (op, es) := arg_shift NEG ws [:: e ] in
      le_issue_aop op es
  | _ =>
      le_skip
  end.

(* Recognize a multiplication whose product can be fused into MADD/MSUB at
   width [ws]: any product at width at least [ws] qualifies, since only the
   low [ws] bits of the result are kept. *)
Definition is_mul (ws : wsize) (e : pexpr) : option (pexpr * pexpr) :=
  if e is Papp2 (Omul (Op_w ws')) x y
  then if (ws <= ws')%CMP then Some (x, y) else None
  else None.

(* Accept a shift amount that is either a compile-time constant already in
   [0, wsize) or an expression explicitly masked to the operand size
   ([a & (wsize_bits - 1)]), as on x86 and RISC-V. In the masked case the
   mask is dropped: the A64 register shifts reduce the amount modulo the
   operand size, which subsumes it. *)
Definition check_shift_expr (ws : wsize) (e : pexpr) : option pexpr :=
  if is_wconst U8 e is Some n
  then
    if n == wand n (wrepr U8 (wsize_bits ws - 1)) then Some e else None
  else
    match e with
    | Papp2 (Oland _) a b =>
        if is_wconst U8 b is Some n
        then if n == wrepr U8 (wsize_bits ws - 1) then Some a else None
        else None
    | _ => None
    end.

Definition lower_Papp2_op
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) :
  option (armv8a_mnemonic * pexpr * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oadd (Op_w _) =>
      if is_mul ws e0 is Some (x, y)
      then Some (MADD, x, [:: y; e1 ])
      else if is_mul ws e1 is Some (x, y)
      then Some (MADD, x, [:: y; e0 ])
      else
      Some (ADD, e0, [:: e1 ])
  | Omul (Op_w _) =>
      Some (MUL, e0, [:: e1 ])
  | Osub (Op_w _) =>
      if is_mul ws e1 is Some (x, y)
      then Some (MSUB, x, [:: y; e0 ])
      else
        Some (SUB, e0, [:: e1 ])
  | Odiv Signed (Op_w ws') =>
      let%opt _ := oassert (ws' == ws) in
      Some (SDIV, e0, [:: e1 ])
  | Odiv Unsigned (Op_w ws') =>
      let%opt _ := oassert (ws' == ws) in
      Some (UDIV, e0, [:: e1 ])
  | Oland _ =>
      Some (AND, e0, [:: e1 ])
  | Olor _ =>
      Some (ORR, e0, [:: e1 ])
  | Olxor _ =>
      Some (EOR, e0, [:: e1 ])
  (* Logical/arithmetic shifts are NOT lowered to a bare A64 shift for an
     arbitrary amount: the register form of LSR/LSL/ASR shifts by
     [amount mod wsize], whereas the Jasmin source shifts clamp the amount
     to [wsize] (shifting all bits out yields 0). The two disagree once the
     amount reaches [wsize]. As on x86 and RISC-V ([check_shift_amount]
     there), we accept an amount that is either a compile-time constant in
     [0, wsize) or an expression explicitly masked to the operand size
     ([a & (wsize_bits - 1)]); the mask is subsumed by the hardware modulus
     and is dropped. Rotates ([Oror]/[Orol]) are exempt: rotation is
     periodic, so [mod] is already the intended semantics. *)
  | Olsr ws' =>
      let%opt _ := oassert (ws' == ws) in
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else
        let%opt e1' := check_shift_expr ws e1 in
        Some (LSR, e0, [:: e1' ])
  | Olsl (Op_w ws') =>
      let%opt _ := oassert (ws' == ws) in
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else
        let%opt e1' := check_shift_expr ws e1 in
        Some (LSL, e0, [:: e1' ])
  | Oasr (Op_w ws') =>
      let%opt _ := oassert (ws' == ws) in
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else
        let%opt e1' := check_shift_expr ws e1 in
        Some (ASR, e0, [:: e1' ])
  | Oror ws' =>
      let%opt _ := oassert (ws' == ws) in
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: e1 ])
  | Orol ws' =>
      let%opt _ := oassert (ws' == ws) in
      let%opt c := is_wconst U8 e1 in
      if c == 0%w then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: wconst (wrepr U8 (wsize_bits ws) - c)%w ])
  | _ =>
      None
  end.

(* Additions and subtractions of 64-bit immediates that do not fit the
   12-bit (optionally shifted) encoding go through [Oarmv8a_add_large_imm],
   which materializes the immediate with a MOVZ/MOVK sequence at assembly
   generation. *)
Definition large_arith_imm (ws : wsize) (mn : armv8a_mnemonic) (es : pexprs) : option Z :=
  let%opt _ := oassert (ws == U64) in
  let%opt e := if es is [:: e ] then Some e else None in
  let%opt c := is_wconst U64 e in
  let n := wunsigned c in
  if is_arith_small n
  then None
  else
    match mn with
    | ADD => Some n
    | SUB => Some (- n)%Z
    | _ => None
    end.

(* Lower an expression of the form [a <+> b].
   Precondition:
   - [a] is a register.
   - [b] is one of the following:
     + a register.
     + a shifted register.
     + an immediate word. *)
Definition lower_Papp2
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) : low_expr :=
  let%opt (mn, e0', e1') := lower_Papp2_op ws op e0 e1 in
  if large_arith_imm ws mn e1' is Some imm
  then le_issue_extra Oarmv8a_add_large_imm [:: e0'; wconst (wrepr U64 imm) ]
  else
    let '(aop, es) := arg_shift mn ws e1' in
    le_issue_aop aop (e0' :: es).

Definition lower_pexpr_aux (ws : wsize) (e : pexpr) : low_expr :=
  match e with
  | Pvar v => lower_Pvar ws v
  | Pget _ _ _ _ _
  | Pload _ _ _ => lower_load ws e
  | Papp1 op e => lower_Papp1 ws op e
  | Papp2 op a b => lower_Papp2 ws op a b
  | _ => le_skip
  end.

(* A64 has no conditional execution: conditional expressions are lowered
   to CSEL, whose operands must be registers. *)
Definition is_csel_arg (e : pexpr) : bool :=
  if e is Pvar v then ~~ is_var_in_memory (gv v) else false.

Definition lower_Pif
  (vi : var_info) (ws : wsize) (c e0 e1 : pexpr) :
  option (seq instr_r * sopn * seq pexpr) :=
  let%opt _ := chk_ws_reg ws in
  let%opt _ := oassert (is_csel_arg e0 && is_csel_arg e1) in
  let '(pre, c') := lower_condition vi c in
  Some (pre, Oarmv8a (ARMv8A_op CSEL (opts_at ws)), [:: e0; e1; c' ]).

Definition lower_pexpr (vi : var_info) (ws : wsize) (e : pexpr) :
  option (seq instr_r * sopn * seq pexpr) :=
  if e is Pif (aword ws') c e0 e1 then
    let%opt _ := oassert (ws == ws')%CMP in
    lower_Pif vi ws c e0 e1
  else
    no_pre (lower_pexpr_aux ws e).

(* Lower an assignment to memory.
   Precondition:
   - [lv] must be one of the following:
     + a variable in memory.
     + a memory location.
   - [e] must be a register. *)
Definition lower_store (ws : wsize) (e : pexpr) : option (armv8a_asm_op * seq pexpr) :=
  let%opt mn := store_mn_of_wsize ws in
  let osz := if (ws <= U16)%CMP then U64 else ws in
  match e with
  | Pvar _ => Some (ARMv8A_op mn (opts_at osz), [:: e ])
  | _ => None
  end.

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn_word
  (lv : lval) (ws : wsize) (e : pexpr) : option (seq instr_r * copn_args) :=
  let vi := var_info_of_lval lv in
  let%opt (pre, op, es) :=
    if is_lval_in_memory lv
    then
      let%opt (aop, es) := lower_store ws e in
      no_pre (le_issue_aop aop es)
    else lower_pexpr vi ws e
  in
  Some (pre, ([:: lv ], op, es)).

Definition lower_cassgn_bool (lv : lval) (tag : assgn_tag) (e : pexpr) : option (seq instr_r) :=
  let vi := var_info_of_lval lv in
  let%opt (lvs, op, es, c) := lower_condition_pexpr vi e in
  Some [:: Copn lvs tag op es; Cassgn lv AT_inline abool c ].

(* -------------------------------------------------------------------- *)
(* Lowering of architecture-specific operations. *)

Definition isLnone x : bool := if x is Lnone _ _ then true else false.

Definition lower_add_carry
  (lvs : seq lval) (es : seq pexpr) : option copn_args :=
  match lvs, es with
  | [:: cf; r ], [:: x; y; b ] =>
      let cf_not_none := ~~ isLnone cf in
      let%opt (mn, es') :=
        match b with
        | Pbool false => Some ((if cf_not_none then ADDS else ADD), [:: x; y ])
        | Pvar _ => Some ((if cf_not_none then ADCS else ADC), es)
        | _ => None
        end
      in
      let lnoneb := Lnone dummy_var_info abool in
      let lvs' := if cf_not_none then [:: lnoneb; lnoneb; cf; lnoneb; r ] else [:: r ] in
      Some (lvs', Oasm (BaseOp (None, ARMv8A_op mn default_opts)), es')
  | _, _ =>
      None
  end.

Definition with_shift (opts : armv8a_options) sh :=
  {| has_shift := Some sh; opts_size := opts_size opts; |}.

Definition lower_base_op
  (lvs : seq lval) (aop : armv8a_asm_op) (es : seq pexpr) : option copn_args :=
  let: ARMv8A_op mn opts := aop in
  let ws := opts_size opts in
  if has_shift opts != None
  then
    let%opt _ := oassert (mn \in has_shift_mnemonics) in
    Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es)
  else
    if mn \in [:: MVN; NEG ]
    then
      match es with
      | x :: rest =>
          if get_arg_shift ws [:: x ] is Some (ebase, sh, esham)
          then
            if shift_allowed mn sh
            then Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn (with_shift opts sh))), ebase :: esham :: rest)
            else Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es)
          else Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es)
      | _ => None end
    else if mn \in [:: ADD; ADDS; SUB; SUBS; AND; EOR; ORR; CMP; TST ]
    then
      match es with
      | x :: y :: rest =>
          if get_arg_shift ws [:: y ] is Some (ebase, sh, esham)
          then
            if shift_allowed mn sh
            then Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn (with_shift opts sh))), x :: ebase :: esham :: rest)
            else Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es)
          else Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es)
      | _ => None end
    else None.

Definition lower_swap ty lvs es : option copn_args :=
  match ty with
  | aword sz =>
    if (sz == U64)%CMP then
      Some (lvs, Oasm (ExtOp (Oarmv8a_swap sz)), es)
    else None
  | aarr _ _ =>
      Some (lvs, Opseudo_op (Oswap ty), es)
  | _ => None
  end.

Definition lower_pseudo_operator
  (lvs : seq lval) (op : pseudo_operator) (es : seq pexpr) : option copn_args :=
  match op with
  | Oaddcarry U64 => lower_add_carry lvs es
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

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      let oirs :=
        match ty with
        | aword ws =>
            let%opt (pre, (lvs, op, es)) := lower_cassgn_word lv ws e in
            Some (pre ++ [:: Copn lvs tag op es ])
        | abool => lower_cassgn_bool lv tag e
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
      let '(pre, e') := lower_condition (var_info_of_ii ii) e in
      let c1' := List.flat_map lower_i c1 in
      let c2' := List.flat_map lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])

  | Cfor v r c =>
      let c' := List.flat_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e info c1 =>
      let '(pre, e') := lower_condition (var_info_of_ii info) e in
      let c0' := List.flat_map lower_i c0 in
      let c1' := List.flat_map lower_i c1 in
      [:: MkI ii (Cwhile a (c0' ++ map (MkI info) pre) e' info c1') ]

  | _ =>
      [:: i ]
  end.

End ARMV8A_LOWERING.

End Section.
