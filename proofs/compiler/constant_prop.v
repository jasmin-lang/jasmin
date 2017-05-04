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
Require Import expr ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

(* FIXME move this *)
Fixpoint eq_expr e e' := 
  match e, e' with
  | Pconst z      , Pconst z'         => z == z'
  | Pbool  b      , Pbool  b'         => b == b'
  (* FIXME if e1, e2 = Pconst we can compute the cast *)
  | Pcast  e      , Pcast  e'         => eq_expr e e' 
  | Pvar   x      , Pvar   x'         => v_var x == v_var x'
  | Pget   x e    , Pget   x' e'      => (v_var x == v_var x') && eq_expr e e' 
  | Pload  x e    , Pload  x' e'      => (v_var x == v_var x') && eq_expr e e' 
  | Pnot   e      , Pnot   e'         => eq_expr e e'
  | Papp2  o e1 e2, Papp2  o' e1' e2' => (o == o') && eq_expr e1 e1' && eq_expr e2 e2'
  | _             , _                 => false
  end.

Definition snot (e:pexpr) : pexpr := 
  match e with
  | Pbool b => negb b
  | Pnot  e => e 
  | _       => Pnot e
  end.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor e1 e2 := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2 
  end.

Definition sadd e1 e2:= 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 + n2)
  | Some n, _ => 
    if (n == 0)%Z then e2 else Papp2 Oadd e1 e2
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 Oadd e1 e2
  | _, _ => Papp2 Oadd e1 e2
  end.

Definition ssub e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 Osub e1 e2
  | _, _ => Papp2 Osub e1 e2
  end.

Definition smul e1 e2:= 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 * n2)
  | Some n, _ => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e2 
    else Papp2 Omul e1 e2
  | _, Some n => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e1
    else Papp2 Omul e1 e2
  | _, _ => Papp2 Omul e1 e2
  end.

(* FIXME: improve optimisation for word *)
Definition s_eq ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true else Papp2 (Oeq ty) e1 e2.

Definition sneq ty e1 e2 := 
  if eq_expr e1 e2 then Pbool false else Papp2 (Oneq ty) e1 e2.

Definition slt ty e1 e2 := 
  if eq_expr e1 e2 then Pbool false 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <? n2)%Z
  | _      , _       => Papp2 (Olt ty) e1 e2 
  end.

Definition sle ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <=? n2)%Z
  | _      , _       => Papp2 (Ole ty) e1 e2 
  end.

Definition sgt ty e1 e2 := 
  if eq_expr e1 e2 then Pbool false 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >? n2)%Z
  | _      , _       => Papp2 (Ogt ty) e1 e2 
  end.

Definition sge ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >=? n2)%Z
  | _      , _       => Papp2 (Oge ty) e1 e2 
  end.

Definition s_op2 o e1 e2 := 
  match o with 
  | Oand    => sand e1 e2 
  | Oor     => sor  e1 e2
  | Oadd    => sadd e1 e2
  | Osub    => ssub e1 e2
  | Omul    => smul e1 e2
  | Oeq  ty => s_eq ty e1 e2
  | Oneq ty => sneq ty e1 e2
  | Olt  ty => slt  ty e1 e2
  | Ole  ty => sle  ty e1 e2
  | Ogt  ty => sgt  ty e1 e2
  | Oge  ty => sge  ty e1 e2
  end.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)

Local Notation cpm := (Mvar.t Z).

Fixpoint const_prop_e (m:cpm) e :=
  match e with
  | Pconst _  => e
  | Pbool  _  => e
  | Pcast e   => Pcast (const_prop_e m e)
  | Pvar  x   => if Mvar.get m x is Some n then Pconst n else e
  | Pget  x e => Pget x (const_prop_e m e)
  | Pload x e => Pload x (const_prop_e m e)
  | Pnot  e   => snot e
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  end.

Definition empty_cpm : cpm := @Mvar.empty Z.

Definition merge_cpm : cpm -> cpm -> cpm := 
  Mvar.map2 (fun _ (o1 o2: option Z) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:cpm) (s:Sv.t): cpm :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Definition const_prop_rv (m:cpm) (rv:lval) : cpm * lval := 
  match rv with 
  | Lnone _   => (m, rv)
  | Lvar  x   => (Mvar.remove m x, rv)
    (* TODO : FIXME should we do more on x, in particular if x is a known value *)
  | Lmem  x e => (m, Lmem x (const_prop_e m e))
  | Laset x e => (Mvar.remove m x, Laset x (const_prop_e m e))
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals := 
  match rvs with
  | [::] => (m, [::])
  | rv::rvs => 
    let (m,rv)  := const_prop_rv m rv in 
    let (m,rvs) := const_prop_rvs m rvs in
    (m, rv::rvs)
  end.

Definition add_cpm (m:cpm) (rv:lval) tag e := 
  if rv is Lvar x then
    if tag is AT_inline then 
      if is_const e is Some n then Mvar.set m x n else m 
    else m
  else m. 
                           
Section CMD.

  Variable const_prop_i : cpm -> instr -> cpm * cmd.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd := 
  match ir with
  | Cassgn x tag e => 
    let e := const_prop_e m e in 
    let (m,x) := const_prop_rv m x in
    let m := add_cpm m x tag e in
    (m, [:: MkI ii (Cassgn x tag e)])

  | Copn xs o es =>
    let es := map (const_prop_e m) es in
    let (m,xs) := const_prop_rvs m xs in
    (m, [:: MkI ii (Copn xs o es) ])

  | Cif b c1 c2 => 
    let b := const_prop_e m b in
    match is_bool b with
    | Some b => 
      let c := if b then c1 else c2 in 
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ])
    end

  | Cfor x (dir, e1, e2) c =>
    let e1 := const_prop_e m e1 in
    let e2 := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ])

  | Cwhile c e c' =>
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    let (_,c') := const_prop const_prop_i m c' in
    (m, [:: MkI ii (Cwhile c (const_prop_e m e) c')])

  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let (m,xs) := const_prop_rvs m xs in
    (m, [:: MkI ii (Ccall fi xs f es) ])
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,p,c,r) := f in
  let (_, c) := const_prop const_prop_i empty_cpm c in
  MkFun ii p c r.

Definition const_prop_prog (p:prog) : prog := map_prog const_prop_fun p.

