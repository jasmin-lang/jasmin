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
  riscv_decl
  riscv_params_core
  riscv_instr_decl
  riscv_extra.

Section Section.
Context {atoI : arch_toIdent}.

(* TODO : Review *)
Definition chk_ws_reg (ws : wsize) : option unit :=
  oassert (ws == reg_size)%CMP.

(* Ensure shift amount is less than 32 *)
Definition check_shift_amount e :=
  if is_wconst U8 e is Some n
  then if n == wand n (wrepr U8 31) then Some e else None
  else match e with
  | Papp2 (Oland _) a b =>
      if is_wconst U8 b is Some n
      then if n == wrepr U8 31 then Some a else None
      else None
  | _ => None 
  end.

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : option(riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oword_of_int _ =>
    if is_const e is Some _
      then  Some(BaseOp (None, LI), [:: Papp1 (Oword_of_int U32) e])
    else None
  | Osignext U32 ws' =>
      let%opt _ := oassert (ws' <= U32)%CMP in
      let%opt _ := oassert (is_load e) in
      Some (BaseOp(None, LOAD Signed ws'), [:: e ])
  | Ozeroext U32 ws' =>
      let%opt _ := oassert (ws' <= U16)%CMP in
      let%opt _ := oassert (is_load e) in
      Some (BaseOp(None, LOAD Unsigned ws'), [:: e ])    
  | Olnot U32 =>
      Some(BaseOp (None, NOT), [:: e])
  | Oneg (Op_w U32) =>
      Some(BaseOp (None, NEG), [:: e])
  | _ =>
      None
  end.

(* RISC-V only handles immediates lower than 2ˆ12 for I type instructions *)
Definition decide_op_reg_imm
  (ws : wsize) (e0 e1: pexpr) (op_reg_reg op_reg_imm : riscv_extended_op) : 
  option (riscv_extended_op * pexprs) :=
  match is_wconst ws e1 with
  | Some (word) => 
    if is_arith_small (wsigned word) then
    Some(op_reg_imm, [::e0; e1])
    else None
  | _ => Some(op_reg_reg, [::e0; e1])
  end.

Definition insert_minus  (e1: pexpr) : option pexpr :=
match e1 with  
  | Papp1 (Oword_of_int sz) (Pconst n) => 
    Some(Papp1 (Oword_of_int sz) (Pconst (- n)))
  | _ => None
end.

(* RISC-V only handles immediates lower than 2ˆ12 for I type instructions *)
Definition decide_op_reg_imm_neg
  (ws : wsize) (e0 e1: pexpr) (op_reg_reg op_reg_imm : riscv_extended_op) : 
  option (riscv_extended_op * pexprs) :=
  match is_wconst ws e1 with
  | Some (word) => 
    if is_arith_small_neg (wsigned word) then
    let%opt e1:= insert_minus e1 in
    Some(op_reg_imm, [::e0; e1])
    else None
  | _ => Some(op_reg_reg, [::e0; e1])
  end.

Definition lower_Papp2
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) :
  option (riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oadd (Op_w _) => decide_op_reg_imm U32 e0 e1 (BaseOp(None, ADD)) (BaseOp(None, ADDI))
  | Omul (Op_w _) => Some (BaseOp (None, MUL), [:: e0; e1])
  | Osub (Op_w _) => decide_op_reg_imm_neg U32 e0 e1 (BaseOp(None, SUB)) (BaseOp(None, ADDI))
  | Odiv sg (Op_w U32) =>
    let o := if sg is Signed then DIV else DIVU in
    Some (BaseOp (None, o), [:: e0; e1])
  | Omod sg (Op_w U32) =>
    let o := if sg is Signed then REM else REMU in
    Some (BaseOp (None, o), [:: e0; e1])
  | Oland _ => decide_op_reg_imm U32 e0 e1 (BaseOp(None, AND)) (BaseOp(None, ANDI))
  | Olor _ => decide_op_reg_imm U32 e0 e1 (BaseOp(None, OR)) (BaseOp(None, ORI))
  | Olxor _ => decide_op_reg_imm U32 e0 e1 (BaseOp(None, XOR)) (BaseOp(None, XORI))
  | Olsr U32 =>
    if check_shift_amount e1 is Some(e1) then
      let op := if is_wconst U8 e1 then SRLI else SRL in
      Some (BaseOp (None, op), [:: e0; e1])
    else None
  | Olsl (Op_w _) =>
    if check_shift_amount e1 is Some(e1) then
      let op := if is_wconst U8 e1 then SLLI else SLL in
      Some (BaseOp (None, op), [:: e0; e1])
    else None
  | Oasr (Op_w U32) =>
    if check_shift_amount e1 is Some(e1) then
      let op := if is_wconst U8 e1 then SRAI else SRA in
      Some (BaseOp (None, op), [:: e0; e1])
    else None
  | _ =>
      None
  end.

(* Lower an expression of the form [(ws)[v + e]] or [tab[ws e]]. *)
Definition lower_load (ws: wsize) (e: pexpr) : option(riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  Some (BaseOp (None, LOAD Signed U32), [:: e ]).

(* Lower an expression of the form [v].
   Precondition:
   - [v] is a one of the following:
     + a register.
     + a stack variable. *)
Definition lower_Pvar (ws : wsize) (v : gvar) : option(riscv_extended_op * pexprs) :=
    (* For now, only 32 bits can be read from memory or upon move, signed / unsigned has no effect on load or move *)
    if ws != U32 
        then None 
    else
        let op := if is_var_in_memory (gv v) then LOAD Signed U32 else MV in
        Some (BaseOp (None, op), [:: Pvar v ]).

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn
  (lv : lval) (ws : wsize) (e : pexpr) : option (copn_args) :=
  if is_lval_in_memory lv
    then 
      if (ws <= U32)%CMP
        then
          Some ([:: lv], Oriscv (STORE ws), [:: e])
        else
          None
  else
  let%opt (op, e) :=
    match e with
    | Pvar v => lower_Pvar ws v
    | Pget _ _ _ _ _
    | Pload _ _ _ _ => lower_load ws e
    | Papp1 op e => lower_Papp1 ws op e
    | Papp2 op a b => lower_Papp2 ws op a b
    | _ => None
    end
    in Some ([:: lv], Oasm op, e).

Definition lower_swap ty lvs es : option (seq copn_args) := 
  match ty with
  | sword sz => 
    if (sz <= U32)%CMP then 
      Some([:: (lvs, Oasm (ExtOp (SWAP sz)), es)])
    else None
  | sarr _ => 
      Some([:: (lvs, Opseudo_op (Oswap ty), es)])
  | _ => None
  end.

Definition lower_mulu (lvs : seq lval) (es : seq pexpr) : option (seq copn_args):=  
  match lvs, es with
  | [:: Lvar r1; Lvar r2 ], [:: Pvar x ; Pvar y ] =>
    if (r1 == x.(gv):>var) || (r1 == y.(gv):>var) then
    None
    else
    (* Arbitrary choice : r1 computed before r2*)  
    Some [::
      ([:: Lvar r1], Oasm(BaseOp (None, MULHU)), es);
      ([:: Lvar r2], Oasm(BaseOp (None, MUL)), es)]
  | _, _ => None
  end.

Definition lower_pseudo_operator
  (lvs : seq lval) (op : pseudo_operator) (es : seq pexpr) : option (seq copn_args) :=
  match op with
  | Oswap ty => lower_swap ty lvs es
  | Omulu U32 => lower_mulu lvs es
  | _ => None
  end.

Definition lower_copn
  (lvs : seq lval) (op : sopn) (es : seq pexpr) : option (seq copn_args) :=
  match op with
  | Opseudo_op pop => lower_pseudo_operator lvs pop es
  | _ => None
  end.

(* -------------------------------------------------------------------- *)

Definition lowering_options := unit.

(* Applied to every jasmin lines, cmd is a list of instructions *)
Fixpoint lower_i (i : instr) : cmd :=
(* ii : instruction info, ir : instruction itself *)
  let '(MkI ii ir) := i in
  match ir with
  (* ty is the type of the assign, lv and e *)
  | Cassgn lv tg ty e =>
      let oirs :=
        match ty with
        | sword ws =>
            let%opt (lvs, op, es) := lower_cassgn lv ws e in
            Some ([:: Copn lvs tg op es ])
        | _ => None
        end
      in
      let irs := if oirs is Some irs then irs else [:: ir ] in
      (* Reintroduce information instruction *)
      map (MkI ii) irs

 (* Copn : "assembly" instruction pattern matching, required for pseudo instructions or extra instructions *)
  | Copn lvs tag op es =>
      let seq_ir :=
        if lower_copn lvs op es is Some l
        then map (fun '(lvs', op', es') => Copn lvs' tag op' es') l
        else [:: ir]
      in map (MkI ii) seq_ir
      
  | Cif e c1 c2  =>
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
        [:: MkI ii (Cif e c1' c2')]

  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e info c1 =>
      let c0' := conc_map lower_i c0 in
      let c1' := conc_map lower_i c1 in
      [:: MkI ii (Cwhile a c0' e info c1')]

  | _ =>
      [:: i ]
  end.

End Section.
