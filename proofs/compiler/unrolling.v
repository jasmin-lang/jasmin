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
Require Import ZArith expr compiler_util leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd * leak_i_tr) (c:cmd) : cmd * leak_c_tr :=
  List.fold_right (fun i c' => let r := unroll_i i in
                               ((r.1 ++ c'.1), ([:: r.2] ++ c'.2)))
                      ([::], [::]) c.

Definition assgn ii x e := (MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) e)).

Definition assgn' ii x e := (MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) e), LT_ile (LT_seq [:: LT_id; LT_id])).

Fixpoint unroll_i (i:instr) : cmd * leak_i_tr :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => ([:: i ], LT_ikeep)
  | Copn _ _ _ _ => ([:: i ], LT_ikeep)
  | Cif b c1 c2  => let r1 := (unroll_cmd unroll_i c1) in
                    let r2 := (unroll_cmd unroll_i c2) in
                    ([:: MkI ii (Cif b r1.1 r2.1) ],
                     LT_icond LT_id r1.2 r2.2)
  (** FIX NEEDED **)
  | Cfor i (dir, low, hi) c =>
    let c' := unroll_cmd unroll_i c in
    match is_const low, is_const hi with
    | Some vlo, Some vhi =>
      let l := wrange dir vlo vhi in
      let cs := map (fun n => ((assgn ii i (Pconst n)) :: c'.1)) l in 
      (*let cs := map (fun n => assgn ii i (Pconst n) :: c') l in*)
      (flatten cs, LT_ifor_unroll c'.2)
    | _, _       => ([:: MkI ii (Cfor i (dir, low, hi) c'.1) ], LT_ifor LT_id c'.2)
    end
  | Cwhile a c e c'  => let r1 :=  (unroll_cmd unroll_i c) in
                        let r2 :=  (unroll_cmd unroll_i c') in 
    ([:: MkI ii (Cwhile a r1.1 e r2.1) ], LT_iwhile r1.2 LT_id r2.2)
     
  | Ccall _ _ _ _  => ([:: i ], LT_icall LT_id LT_id)
  end.

Definition unroll_fun (f:fundef) :=
  let 'MkFun ii si p c so r := f in
  let rs := (unroll_cmd unroll_i c) in 
  (MkFun ii si p rs.1 so r, rs.2).

Definition unroll_prog (p:prog) : (prog * leak_f_tr) :=
  let fs := map_prog_leak unroll_fun (p_funcs p) in 
  (*let fundefs := map snd (p_funcs p) in (* seq of fundefs *)
  let funnames := map fst (p_funcs p) in
  let r := map unroll_fun fundefs in (* output of applying const_prop_fun to the fundefs from p *)
  let rfds := map fst r in
  let rlts := map snd r in 
  let Fs := zip funnames rlts in
  let funcs := zip funnames rfds in *)
  ({| p_globs := p_globs p; p_funcs := fs.1|}, fs.2).
