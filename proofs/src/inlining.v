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

Print pexpr.
Definition destr_pair t1 t2 (p:pexpr (t1 ** t2)) : option (pexpr t1 * pexpr t2).
case H: _ / p => [ ? | ? | ???? | ??? o e1 e2| ???????? ].
+ exact None. + exact None. + exact None. 
+ (case:o H e1 e2 => [||||||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *; 
  exact None.
exact None. 
Defined.

Definition efst t1 t2 (p:pexpr (t1 ** t2)) : pexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Papp1 (Ofst _ _) p
  end.

Definition esnd t1 t2 (p:pexpr (t1 ** t2)) : pexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Papp1 (Osnd _ _) p
  end.
Print cmd.

Fixpoint assgn_tuple t (rv:rval t) : pexpr t -> cmd :=
  match rv in rval t0 return pexpr t0 -> cmd with
  | Rvar x              => fun e => [:: assgn (Rvar x) e]
  | Rpair t1 t2 rv1 rv2 => fun e => assgn_tuple rv1 (efst e) ++ assgn_tuple rv2 (esnd e)
  end.

Fixpoint rval2pe t (rv:rval t) := 
  match rv in rval t_ return pexpr t_ with
  | Rvar x              => x
  | Rpair t1 t2 rv1 rv2 => Papp2 (Opair t1 t2) (rval2pe rv1) (rval2pe rv2)
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

