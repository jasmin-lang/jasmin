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
Require Import expr ZArith sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot_bool (e:pexpr) := 
  match e with
  | Pbool b      => negb b
  | Papp1 Onot e => e 
  | _            => Papp1 Onot e
  end.

(* FIXME: make this smart constructor smarter *)
Definition sneg (e: pexpr) := Papp1 Oneg e.

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

(* FIXME improve this *)
Definition snot_w e := Papp1 Olnot e.

Definition s_op1 o e := 
  match o with
  | Onot  => snot_bool e 
  | Olnot => snot_w e
  | Oneg  => sneg e
  | Oarr_init => Papp1 Oarr_init e
  end.

(* ------------------------------------------------------------------------ *)

Definition sadd_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 + n2)
  | Some n, _ => 
    if (n == 0)%Z then e2 else Papp2 (Oadd Op_int) e1 e2
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 (Oadd Op_int) e1 e2
  | _, _ => Papp2 (Oadd Op_int) e1 e2
  end.

Definition sadd_w e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => 
    wconst (iword_add n1 n2)
  | Some n, _ => 
    if (tobase n == 0)%Z then e2 else Papp2 (Oadd Op_w) e1 e2
  | _, Some n => 
    if (tobase n == 0)%Z then e1 else Papp2 (Oadd Op_w) e1 e2
  | _, _ => Papp2 (Oadd Op_w) e1 e2
  end.

Definition sadd ty :=
  match ty with
  | Op_int => sadd_int
  | Op_w   => sadd_w
  end.

Definition ssub_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 (Osub Op_int) e1 e2
  | _, _ => Papp2 (Osub Op_int) e1 e2
  end.

Definition ssub_w e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => wconst (iword_sub n1 n2)
  | _, Some n => 
    if (tobase n == 0)%Z then e1 else Papp2 (Osub Op_w) e1 e2
  | _, _ => Papp2 (Osub Op_w) e1 e2
  end.

Definition ssub ty := 
  match ty with
  | Op_int => ssub_int
  | Op_w   => ssub_w
  end.

Definition smul_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 * n2)
  | Some n, _ => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e2 
    else Papp2 (Omul Op_int) e1 e2
  | _, Some n => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e1
    else Papp2 (Omul Op_int) e1 e2
  | _, _ => Papp2 (Omul Op_int) e1 e2
  end.

Definition smul_w e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => wconst (iword_mul n1 n2)
  | Some n, _ => 
    let n := tobase n in
    if (n == 0)%Z then wconst 0
    else if (n == 1)%Z then e2 
    else Papp2 (Omul Op_w) (wconst n) e2
  | _, Some n => 
    let n := tobase n in
    if (n == 0)%Z then wconst 0
    else if (n == 1)%Z then e1
    else Papp2 (Omul Op_w) e1 (wconst n)
  | _, _ => Papp2 (Omul Op_w) e1 e2
  end.

Definition smul ty := 
  match ty with
  | Op_int => smul_int
  | Op_w   => smul_w
  end.

Definition s_eq ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else 
    match ty with
    | Cmp_int =>
      match is_const e1, is_const e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end 
    | Cmp_sw | Cmp_uw =>
      match is_wconst e1, is_wconst e2 with
      | Some i1, Some i2 => Pbool (iword_eqb i1 i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    end.

Definition sneq ty e1 e2 := 
  match is_bool (s_eq ty e1 e2) with
  | Some b => Pbool (~~ b)
  | None      => Papp2 (Oneq ty) e1 e2
  end.

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

Definition sbitw_int i z e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (z n1 n2)
  | _, _ => Papp2 (i Op_int) e1 e2
  end.

Definition sbitw_w i z e1 e2 :=
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => wconst (z (I64.repr n1) (I64.repr n2))
  (* TODO: could be improved when one operand is known *)
  | _, _ => Papp2 (i Op_w) e1 e2
  end.

Definition sbitw i z ty :=
  match ty with
  | Op_int => sbitw_int i z
  | Op_w => sbitw_w i z
  end.

Definition sland := sbitw Oland Z.land.
Definition slor := sbitw Olor Z.lor.
Definition slxor := sbitw Olxor Z.lxor.

Definition slsr  e1 e2 := 
  sbitw_w (fun _ => Olsr) sem_lsr e1 e2.

Definition slsl  e1 e2 := 
   sbitw_w (fun _ => Olsl) sem_lsl e1 e2.

Definition sasr  e1 e2 := 
  sbitw_w (fun _ => Oasr) sem_asr e1 e2.

Definition s_op2 o e1 e2 := 
  match o with 
  | Oand    => sand e1 e2 
  | Oor     => sor  e1 e2
  | Oadd ty => sadd ty e1 e2
  | Osub ty => ssub ty e1 e2
  | Omul ty => smul ty e1 e2
  | Oeq  ty => s_eq ty e1 e2
  | Oneq ty => sneq ty e1 e2
  | Olt  ty => slt  ty e1 e2
  | Ole  ty => sle  ty e1 e2
  | Ogt  ty => sgt  ty e1 e2
  | Oge  ty => sge  ty e1 e2
  | Oland ty => sland ty e1 e2
  | Olor ty => slor ty e1 e2
  | Olxor ty => slxor ty e1 e2
  | Olsr    => slsr  e1 e2
  | Olsl    => slsl  e1 e2
  | Oasr    => sasr  e1 e2
  end.

Definition s_if e e1 e2 := 
  match is_bool e with
  | Some b => if b then e1 else e2
  | None   => Pif e e1 e2
  end.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)

Inductive const_v :=
  | Cint of Z
  | Cword of Z.
 
Scheme Equality for const_v.

Lemma const_v_eq_axiom : Equality.axiom const_v_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_const_v_dec_bl.
  by apply: internal_const_v_dec_lb.
Qed.

Definition const_v_eqMixin     := Equality.Mixin const_v_eq_axiom.
Canonical  const_v_eqType      := Eval hnf in EqType const_v const_v_eqMixin.

Local Notation cpm := (Mvar.t const_v).

Definition const v := 
  match v with
  | Cint z  => Pconst z
  | Cword z => wconst z
  end.

Fixpoint const_prop_e (m:cpm) e :=
  match e with
  | Pconst _      => e
  | Pbool  _      => e
  | Pcast e       => Pcast (const_prop_e m e)
  | Pvar  x       => if Mvar.get m x is Some n then const n else e
  | Pglobal _ => e
  | Pget  x e     => Pget x (const_prop_e m e)
  | Pload x e     => Pload x (const_prop_e m e)
  | Papp1 o e     => s_op1 o (const_prop_e m e)
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  | Pif e e1 e2   => s_if (const_prop_e m e) (const_prop_e m e1) (const_prop_e m e2)
  end.

Definition empty_cpm : cpm := @Mvar.empty const_v.

Definition merge_cpm : cpm -> cpm -> cpm := 
  Mvar.map2 (fun _ (o1 o2: option const_v) => 
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
  | Lnone _ _ => (m, rv)
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
      match e with
      | Pconst z =>  Mvar.set m x (Cint z)
      | Pcast (Pconst z) =>  Mvar.set m x (Cword z)
      | _ => m
      end
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

  | Copn xs t o es =>
    (* TODO: Improve this *)
    let es := map (const_prop_e m) es in
    let (m,xs) := const_prop_rvs m xs in
    (m, [:: MkI ii (Copn xs t o es) ])

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
    let (m',c) := const_prop const_prop_i m c in
    let e := const_prop_e m' e in
    let (_,c') := const_prop const_prop_i m' c' in
    let cw := 
      match is_bool e with
      | Some false => c
      | _          => [:: MkI ii (Cwhile c e c')]
      end in
    (m', cw)
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

