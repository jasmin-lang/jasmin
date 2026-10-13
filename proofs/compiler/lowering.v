Require Import compiler_util expr.

Section LOWERING.

Definition fresh_vars : Type := string -> atype -> Ident.ident.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (lower_i0 :
      (instr_info -> warning_msg -> instr_info)
    -> fresh_vars
    -> instr
    -> cmd)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  {pT : progT}
  (all_fresh_vars : seq Ident.ident)
  (fvars : Sv.t).

Definition disj_fvars (x : Sv.t) : bool := disjoint x fvars.

Definition fvars_correct (fds : fun_decls) : bool :=
  disj_fvars (vars_p fds) && uniq all_fresh_vars.

Definition is_lval_in_memory (x : lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v => is_var_in_memory v
  | Laset _ _ _ v _ => is_var_in_memory v
  | Lasub _ _ _ v _ => is_var_in_memory v
  | Lmem _ _ _ _ => true
  end.

Notation lower_i :=
  (lower_i0 warning fv).

Definition lower_cmd  (c : cmd) : cmd :=
  List.flat_map lower_i c.

Definition lower_fd (fd : fundef) : fundef :=
  with_body fd (lower_cmd (f_body fd)).

Definition lower_prog (p : prog) :=
  map_prog lower_fd p.

End LOWERING.

(* -------------------------------------------------------------------- *)
(* Patterns shared by the lowering passes of the back-ends. *)

(* A complemented operand [!a], at any width: the operator that consumes it
   truncates it to its own width, which commutes with the complement. *)
Definition is_lnot (e : pexpr) : option pexpr :=
  match e with
  | Papp1 (Olnot _) a => Some a
  | _ => None
  end.

(* The operands of a conjunction, one of which is complemented:
   [is_andn a b = Some (x, y)] means that [a & b] is [!x & y], whatever the
   order of the operands. *)
Definition is_andn (a b : pexpr) : option (pexpr * pexpr) :=
  match is_lnot a, is_lnot b with
  | Some a, _ => Some (a, b)
  | None, Some b => Some (b, a)
  | None, None => None
  end.
