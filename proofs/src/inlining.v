(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings  dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope fset.
Local Open Scope seq_scope.

(* ** inlining
 * -------------------------------------------------------------------- *)

Fixpoint assgn_tuple t (rv:rval t) : pexpr t -> cmd :=
  match rv in rval t0 return pexpr t0 -> cmd with
  | Rvar x              => fun e => [:: assgn (Rvar x) e]
  | Rpair t1 t2 rv1 rv2 => fun e => assgn_tuple rv1 (efst e) ++ assgn_tuple rv2 (esnd e)
  end.


Definition inline_cmd (inline_i: instr -> cmd) (c:cmd) := 
  List.fold_right (fun i c' => inline_i i ++ c') [::] c.

Definition inline_call inline_i sta str (rv_res : rval str) fd (pe_arg : pexpr sta) :=
  match fd in fundef sta str return pexpr sta -> rval str -> cmd with
  | FunDef sta str fa fc fr =>
      fun pe_arg rv_res => 
        assgn_tuple fa pe_arg ++ 
        (inline_cmd inline_i fc ++
         assgn_tuple rv_res (rval2pe fr))
  end pe_arg rv_res.

Fixpoint inline_i (i:instr) : cmd := 
  match i with
  | Cbcmd _     => [::i]
  | Cif b c1 c2 => [::Cif b (inline_cmd inline_i c1) (inline_cmd inline_i c2)]
  | Cfor i rn c => [::Cfor i rn (inline_cmd inline_i c)]
  | Ccall ta tr x fd arg => inline_call inline_i x  fd arg
  end.

Definition inline :=  inline_cmd inline_i.

