(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

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
  | Ccopy _ _ => [:: i ]
  end.

Section Section.

Context {T} {pT:progT T}.

Definition unroll_fun (f:fundef) :=
  let 'MkFun ii si p c so r ev := f in
  MkFun ii si p (unroll_cmd unroll_i c) so r ev.

Definition unroll_prog (p:prog) := map_prog unroll_fun p.

End Section.


