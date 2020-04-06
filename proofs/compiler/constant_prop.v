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
From CoqWord Require Import ssrZ.
Require Import expr ZArith psem.
Import all_ssreflect all_algebra.
Import Utf8.
Import oseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition sword_of_int sz (e: pexpr) :=
  Papp1 (Oword_of_int sz) e.

Definition sint_of_word sz (e: pexpr) :=
  if is_wconst sz e is Some w
  then Pconst (wunsigned w)
  else Papp1 (Oint_of_word sz) e.

Definition ssign_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then Papp1 (Oword_of_int sz) (Pconst (wunsigned (sign_extend sz w)))
  else Papp1 (Osignext sz sz') e.

Definition szero_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then Papp1 (Oword_of_int sz) (Pconst (wunsigned (zero_extend sz w)))
  else Papp1 (Ozeroext sz sz') e.

Definition snot_bool (e:pexpr) :=
  match e with
  | Pbool b      => negb b
  | Papp1 Onot e => e
  | _            => Papp1 Onot e
  end.

Definition snot_w (sz: wsize) (e:pexpr) :=
  match is_wconst sz e with
  | Some n => wconst (wnot n)
  | None   => Papp1 (Olnot sz) e
  end.

Definition sneg_int (e: pexpr) :=
  match e with
  | Pconst z => Pconst (- z)
  | Papp1 (Oneg Op_int) e' => e'
  | _ => Papp1 (Oneg Op_int) e
  end.

Definition sneg_w (sz: wsize) (e:pexpr) :=
  match is_wconst sz e with
  | Some n => wconst (- n)%R
  | None   => Papp1 (Oneg (Op_w sz)) e
  end.

Definition s_op1 o e :=
  match o with
  | Oword_of_int sz => sword_of_int sz e
  | Oint_of_word sz => sint_of_word sz e
  | Osignext sz sz' => ssign_extend sz sz' e
  | Ozeroext sz sz' => szero_extend sz sz' e
  | Onot  => snot_bool e
  | Olnot sz => snot_w sz e
  | Oneg Op_int => sneg_int e
  | Oneg (Op_w sz) => sneg_w sz e
  end.

(* ------------------------------------------------------------------------ *)
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

Definition sadd_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 + n2)
  | Some n, _ => if n == 0%R then e2 else Papp2 (Oadd (Op_w sz)) e1 e2
  | _, Some n => if n == 0%R then e1 else Papp2 (Oadd (Op_w sz)) e1 e2
  | _, _ => Papp2 (Oadd (Op_w sz)) e1 e2
  end.

Definition sadd ty :=
  match ty with
  | Op_int => sadd_int
  | Op_w sz => sadd_w sz
  end.

Definition ssub_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n =>
    if (n == 0)%Z then e1 else Papp2 (Osub Op_int) e1 e2
  | _, _ => Papp2 (Osub Op_int) e1 e2
  end.

Definition ssub_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 - n2)
  | _, Some n => if n == 0%R then e1 else Papp2 (Osub (Op_w sz)) e1 e2
  | _, _ => Papp2 (Osub (Op_w sz)) e1 e2
  end.

Definition ssub ty :=
  match ty with
  | Op_int => ssub_int
  | Op_w sz => ssub_w sz
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

Definition smul_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (n1 * n2)
  | Some n, _ =>
    if n == 0%R then @wconst sz 0
    else if n == 1%R then e2
    else Papp2 (Omul (Op_w sz)) (wconst n) e2
  | _, Some n =>
    if n == 0%R then @wconst sz 0
    else if n == 1%R then e1
    else Papp2 (Omul (Op_w sz)) e1 (wconst n)
  | _, _ => Papp2 (Omul (Op_w sz)) e1 e2
  end.

Definition smul ty :=
  match ty with
  | Op_int => smul_int
  | Op_w sz => smul_w sz
  end.

Definition s_eq ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else
    match ty with
    | Op_int =>
      match is_const e1, is_const e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    | Op_w sz =>
      match is_wconst sz e1, is_wconst sz e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    end.

Definition sneq ty e1 e2 :=
  match is_bool (s_eq ty e1 e2) with
  | Some b => Pbool (~~ b)
  | None      => Papp2 (Oneq ty) e1 e2
  end.

Definition is_cmp_const (ty: cmp_kind) (e: pexpr) : option Z :=
  match ty with
  | Cmp_int => is_const e
  | Cmp_w sg sz =>
    is_wconst sz e >>= λ w,
    Some match sg with
    | Signed => wsigned w
    | Unsigned => wunsigned w
    end
  end%O.

Definition slt ty e1 e2 :=
  if eq_expr e1 e2 then Pbool false
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 <? n2)%Z
  | _      , _       => Papp2 (Olt ty) e1 e2
  end.

Definition sle ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 <=? n2)%Z
  | _      , _       => Papp2 (Ole ty) e1 e2
  end.

Definition sgt ty e1 e2 :=
  if eq_expr e1 e2 then Pbool false
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 >? n2)%Z
  | _      , _       => Papp2 (Ogt ty) e1 e2
  end.

Definition sge ty e1 e2 :=
  if eq_expr e1 e2 then Pbool true
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => Pbool (n1 >=? n2)%Z
  | _      , _       => Papp2 (Oge ty) e1 e2
  end.

Definition sbitw i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => wconst (z sz n1 n2)
  | _, _ => Papp2 (i sz) e1 e2
  end.

Definition soint i f e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 =>  Pconst (f n1 n2)
  | _, _ => Papp2 (i Cmp_int) e1 e2
  end.

Definition sbituw i (z: signedness -> ∀ sz, word sz → word sz → word sz) u sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 =>
    if n2 == 0%R then Papp2 (i (Cmp_w u sz)) e1 e2
    else wconst (z u sz n1 n2)
  | _, _ => Papp2 (i (Cmp_w u sz)) e1 e2
  end.

Definition sdiv ty (e1 e2:pexpr) :=
  match ty with
  | Cmp_int => soint Odiv Z.div e1 e2
  | Cmp_w u sz => sbituw Odiv (signed (@wdiv) (@wdivi)) u sz e1 e2
  end.

Definition smod ty e1 e2 :=
  match ty with
  | Cmp_int => soint Omod Z.modulo e1 e2
  | Cmp_w u sz => sbituw Omod (signed (@wmod) (@wmodi)) u sz e1 e2
  end.

(* TODO: could be improved when one operand is known *)
Definition sland := sbitw Oland (@wand).
Definition slor := sbitw Olor (@wor).
Definition slxor := sbitw Olxor (@wxor).

Definition sbitw8 i (z: ∀ sz, word sz → u8 → word sz) sz e1 e2 :=
  match is_wconst sz e1, is_wconst U8 e2 with
  | Some n1, Some n2 => wconst (z sz n1 n2)
  | _, _ => Papp2 (i sz) e1 e2
  end.

Definition sshr sz e1 e2 :=
  sbitw8 Olsr (@sem_shr) sz e1 e2.

Definition sshl sz e1 e2 :=
   sbitw8 Olsl (@sem_shl) sz e1 e2.

Definition ssar sz e1 e2 :=
  sbitw8 Oasr (@sem_sar) sz e1 e2.

Definition svadd ve sz e1 e2 :=
   sbitw (Ovadd ve) (@sem_vadd ve) sz e1 e2.

Definition svsub ve sz e1 e2 :=
   sbitw (Ovsub ve) (@sem_vsub ve) sz e1 e2.

Definition svmul ve sz e1 e2 :=
  sbitw (Ovmul ve) (@sem_vmul ve) sz e1 e2.


Definition svshr ve sz e1 e2 :=
  sbitw8 (Ovlsr ve) (@sem_vshr ve) sz e1 e2.

Definition svshl ve sz e1 e2 :=
   sbitw8 (Ovlsl ve) (@sem_vshl ve) sz e1 e2.

Definition svsar ve sz e1 e2 :=
  sbitw8 (Ovasr ve) (@sem_vsar ve) sz e1 e2.

Definition s_op2 o e1 e2 :=
  match o with
  | Oand    => sand e1 e2
  | Oor     => sor  e1 e2
  | Oadd ty => sadd ty e1 e2
  | Osub ty => ssub ty e1 e2
  | Omul ty => smul ty e1 e2
  | Odiv ty => sdiv ty e1 e2
  | Omod ty => smod ty e1 e2
  | Oeq  ty => s_eq ty e1 e2
  | Oneq ty => sneq ty e1 e2
  | Olt  ty => slt  ty e1 e2
  | Ole  ty => sle  ty e1 e2
  | Ogt  ty => sgt  ty e1 e2
  | Oge  ty => sge  ty e1 e2
  | Oland sz => sland sz e1 e2
  | Olor sz => slor sz e1 e2
  | Olxor sz => slxor sz e1 e2
  | Olsr sz => sshr sz e1 e2
  | Olsl sz => sshl sz e1 e2
  | Oasr sz => ssar sz e1 e2
  | Ovadd ve sz => svadd ve sz e1 e2
  | Ovsub ve sz => svsub ve sz e1 e2
  | Ovmul ve sz => svmul ve sz e1 e2
  | Ovlsr ve sz => svshr ve sz e1 e2
  | Ovlsl ve sz => svshl ve sz e1 e2
  | Ovasr ve sz => svsar ve sz e1 e2
  end.

Definition force_int e :=
  if e is Pconst z then ok (Vint z) else type_error.

Definition s_opN op es :=
  match mapM force_int es >>= sem_opN op with
  | Ok (Vword sz w) => Papp1 (Oword_of_int sz) (Pconst (wunsigned w))
  | _ => PappN op es
  end.

Definition s_if t e e1 e2 :=
  match is_bool e with
  | Some b => if b then e1 else e2
  | None   => Pif t e e1 e2
  end.

(* ** constant propagation
 * -------------------------------------------------------------------- *)

Variant const_v :=
  | Cint of Z
  | Cword sz `(word sz).

Definition const_v_beq (c1 c2: const_v) : bool :=
  match c1, c2 with
  | Cint z1, Cint z2 => z1 == z2
  | Cword sz1 w1, Cword sz2 w2 =>
    match wsize_eq_dec sz1 sz2 with
    | left e => eq_rect _ word w1 _ e == w2
    | _ => false
    end
  | _, _ => false
  end.

Lemma const_v_eq_axiom : Equality.axiom const_v_beq.
Proof.
case => [ z1 | sz1 w1 ] [ z2 | sz2 w2] /=; try (constructor; congruence).
+ case: eqP => [ -> | ne ]; constructor; congruence.
case: wsize_eq_dec => [ ? | ne ]; last (constructor; congruence).
subst => /=.
by apply:(iffP idP) => [ /eqP | [] ] ->.
Qed.

Definition const_v_eqMixin     := Equality.Mixin const_v_eq_axiom.
Canonical  const_v_eqType      := Eval hnf in EqType const_v const_v_eqMixin.

Local Notation cpm := (Mvar.t const_v).

Definition const v :=
  match v with
  | Cint z  => Pconst z
  | Cword sz z => wconst z
  end.

Fixpoint const_prop_e (m:cpm) e :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _
    => e
  | Pvar  x       => 
    if is_lvar x then
      if Mvar.get m x.(gv) is Some n then const n else e      
    else e
  | Pget aa sz x e => Pget aa sz x (const_prop_e m e)
  | Psub aa sz len x e => Psub aa sz len x (const_prop_e m e)
  | Pload sz x e  => Pload sz x (const_prop_e m e)
  | Papp1 o e     => s_op1 o (const_prop_e m e)
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  | PappN op es   => s_opN op (map (const_prop_e m) es)
  | Pif t e e1 e2 => s_if t (const_prop_e m e) (const_prop_e m e1) (const_prop_e m e2)
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
  | Lnone _ _       => (m, rv)
  | Lvar  x         => (Mvar.remove m x, rv)
  | Lmem  sz x e    => (m, Lmem sz x (const_prop_e m e))
  | Laset aa sz x e => (Mvar.remove m x, Laset aa sz x (const_prop_e m e))
  | Lasub aa sz len x e => (Mvar.remove m x, Lasub aa sz len x (const_prop_e m e))
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals :=
  match rvs with
  | [::] => (m, [::])
  | rv::rvs =>
    let (m,rv)  := const_prop_rv m rv in
    let (m,rvs) := const_prop_rvs m rvs in
    (m, rv::rvs)
  end.

Definition wsize_of_stype (ty: stype) : wsize :=
  if ty is sword sz then sz else U64.

Definition add_cpm (m:cpm) (rv:lval) tag ty e :=
  if rv is Lvar x then
    if tag is AT_inline then
      match e with
      | Pconst z =>  Mvar.set m x (Cint z)
      | Papp1 (Oword_of_int sz') (Pconst z) =>
        let szty := wsize_of_stype ty in
        let w := zero_extend szty (wrepr sz' z) in
        let w :=
            let szx := wsize_of_stype (vtype x) in
            if (szty ≤ szx)%CMP
            then Cword w
            else Cword (zero_extend szx w) in
        Mvar.set m x w
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
  | Cassgn x tag ty e =>
    let e := const_prop_e m e in
    let (m,x) := const_prop_rv m x in
    let m := add_cpm m x tag ty e in
    (m, [:: MkI ii (Cassgn x tag ty e)])

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

  | Cwhile a c e c' =>
    let m := remove_cpm m (write_i ir) in
    let (m',c) := const_prop const_prop_i m c in
    let e := const_prop_e m' e in
    let (_,c') := const_prop const_prop_i m' c' in
    let cw :=
      match is_bool e with
      | Some false => c
      | _          => [:: MkI ii (Cwhile a c e c')]
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

Section Section.

Context {T} {pT:progT T}.

Definition const_prop_fun (f:fundef) :=
  let 'MkFun ii si p c so r ev := f in
  let (_, c) := const_prop const_prop_i empty_cpm c in
  MkFun ii si p c so r ev.

Definition const_prop_prog (p:prog) : prog := map_prog const_prop_fun p.

End Section.
