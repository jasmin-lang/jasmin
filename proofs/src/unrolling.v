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
Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd) (c:cmd) : cmd := 
  List.fold_right (fun i c' => unroll_i i ++ c') [::] c.

Fixpoint unroll_i (i:instr) : cmd := 
  match i with
  | Cbcmd _     => [::i]
  | Cif b c1 c2 => [::Cif b (unroll_cmd unroll_i c1) (unroll_cmd unroll_i c2)]
  | Cfor fi i rn c => 
    match fi, rn with
    | Unroll_for, (dir, Pconst n1, Pconst n2) =>
      let l := 
        if dir is UpTo then 
          List.map (fun i => n1 + N.of_nat i)%num (iota 0 (N.to_nat (n2 - n1)))
        else
          List.map (fun i => n1 - N.of_nat i)%num (iota 0 (N.to_nat (n1 - n2))) in
      let c := unroll_cmd unroll_i c in
      let cs := map (fun n => assgn i (Pconst n) :: c) l in
      flatten cs 
    | Unroll_for, _ => [::Cfor fi i rn (unroll_cmd unroll_i c)]
    | Keep_for  , _ => [::Cfor fi i rn (unroll_cmd unroll_i c)]
    end
  | Ccall ta tr x fd arg => [::Ccall x (unroll_call fd) arg]
  end

with unroll_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r => 
    FunDef p (unroll_cmd unroll_i c) r
  end.



