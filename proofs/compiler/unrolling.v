(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect.
Require Import ZArith expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd) (c:cmd) : cmd :=
  List.fold_right (fun i c' => unroll_i i ++ c') [::] c.

Definition assgn ii x e := MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) e).

Fixpoint unroll_i (i:instr) : cmd :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => [:: i ]
  | Copn _ _ _ _ => [:: i ]
  | Cif b c1 c2  => [:: MkI ii (Cif b (unroll_cmd unroll_i c1) (unroll_cmd unroll_i c2)) ]
  | Cfor i (dir, low, hi) c =>
    let c' := unroll_cmd unroll_i c in
    match is_const low, is_const hi with
    | Some vlo, Some vhi =>
      let l := wrange dir vlo vhi in
      let cs := map (fun n => assgn ii i (Pconst n) :: c') l in
      flatten cs
    | _, _       => [:: MkI ii (Cfor i (dir, low, hi) c') ]
    end
  | Cwhile a c e c'  => [:: MkI ii (Cwhile a (unroll_cmd unroll_i c) e (unroll_cmd unroll_i c')) ]
  | Ccall _ _ _ _  => [:: i ]
  end.

Definition unroll_fun (f:fundef) :=
  let 'MkFun ii si p c so r := f in
  MkFun ii si p (unroll_cmd unroll_i c) so r.

Definition unroll_prog (p:prog) := map_prog unroll_fun p.

