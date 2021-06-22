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
Require Import expr ZArith psem compiler_util.
Require Import dead_code.
Require Export low_memory.
Import all_ssreflect all_algebra.
Import Utf8.
Import oseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)
Definition sword_of_int sz (e: pexpr) :=
  (Papp1 (Oword_of_int sz) e, LT_id).

Definition sint_of_word sz (e: pexpr) :=
  if is_wconst sz e is Some w
  then (Pconst (wunsigned w), LT_remove)
  else (Papp1 (Oint_of_word sz) e, LT_id).

Definition ssign_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (sign_extend sz w))), LT_map [:: LT_remove; LT_id])
  else (Papp1 (Osignext sz sz') e, LT_id).

Definition szero_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (zero_extend sz w))), LT_map [:: LT_remove; LT_id])
  else (Papp1 (Ozeroext sz sz') e, LT_id).

(* not (not e) ==> e *) 
Definition snot_bool (e:pexpr) : (pexpr * leak_e_tr) :=
  match e with
  | Pbool b      => (Pbool (negb b), LT_remove)
  | Papp1 Onot e0 => (e0, LT_compose (LT_subi 0) (LT_subi 0))
  | _            => (Papp1 Onot e, LT_id)
  end.

Definition snot_w (sz: wsize) (e:pexpr) : (pexpr * leak_e_tr) :=
  match is_wconst sz e with
  | Some n => (wconst (wnot n), LT_map[:: LT_remove; LT_id])
  | None   => (Papp1 (Olnot sz) e, LT_id)
  end.

Definition sneg_int (e: pexpr) : (pexpr * leak_e_tr) :=
  match e with
  | Pconst z => (Pconst (- z), LT_remove)
  | Papp1 (Oneg Op_int) e' => (e', LT_compose (LT_subi 0) (LT_subi 0))
  | _ => (Papp1 (Oneg Op_int) e, LT_id)
  end.

Definition sneg_w (sz: wsize) (e:pexpr) : (pexpr * leak_e_tr) :=
  match is_wconst sz e with
  | Some n => (wconst (- n)%R, LT_map[:: LT_remove; LT_remove])
  | None   => (Papp1 (Oneg (Op_w sz)) e, LT_id)
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
  | Some b, _ => if b then (e2, LT_compose (LT_subi 0) (LT_subi 1)) else (Pbool false, LT_remove)
  | _, Some b => if b then (e1, LT_compose (LT_subi 0) (LT_subi 0)) else (Pbool false, LT_remove)
  | _, _      => (Papp2 Oand e1 e2, LT_id)
  end.

Definition sor e1 e2 :=
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then (Pbool true, LT_remove) else (e2, LT_compose (LT_subi 0) (LT_subi 1))
  | _, Some b => if b then (Pbool true, LT_remove) else (e1, LT_compose (LT_subi 0) (LT_subi 0))
  | _, _       => (Papp2 Oor e1 e2, LT_id)
  end.

(* ------------------------------------------------------------------------ *)

Definition sadd_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => (Pconst (n1 + n2), LT_remove)
  | Some n, _ =>
    if (n == 0)%Z then (e2, LT_compose (LT_subi 0) (LT_subi 1))
                  else (Papp2 (Oadd Op_int) e1 e2, LT_id)
  | _, Some n =>
    if (n == 0)%Z then (e1, LT_compose (LT_subi 0) (LT_subi 0))
                  else (Papp2 (Oadd Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Oadd Op_int) e1 e2, LT_id)
  end.

Definition sadd_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 + n2), LT_map[:: LT_remove; LT_id])
  | Some n, _ => if n == 0%R then (e2, LT_compose (LT_subi 0) (LT_subi 1))
                             else (Papp2 (Oadd (Op_w sz)) e1 e2, LT_id)
  | _, Some n => if n == 0%R then (e1, LT_compose (LT_subi 0) (LT_subi 0))
                             else (Papp2 (Oadd (Op_w sz)) e1 e2, LT_id)
  | _, _ => (Papp2 (Oadd (Op_w sz)) e1 e2, LT_id)
  end.

Definition sadd ty :=
  match ty with
  | Op_int => sadd_int
  | Op_w sz => sadd_w sz
  end.

Definition ssub_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => (Pconst (n1 - n2), LT_remove)
  | _, Some n =>
    if (n == 0)%Z then (e1, LT_compose (LT_subi 0) (LT_subi 0))
                  else (Papp2 (Osub Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Osub Op_int) e1 e2, LT_id)
  end.

Definition ssub_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 - n2),  LT_map[:: LT_remove; LT_id])
  | _, Some n => if n == 0%R then (e1, LT_compose (LT_subi 0) (LT_subi 0))
                             else (Papp2 (Osub (Op_w sz)) e1 e2, LT_id)
  | _, _ => (Papp2 (Osub (Op_w sz)) e1 e2, LT_id)
  end.

Definition ssub ty :=
  match ty with
  | Op_int => ssub_int
  | Op_w sz => ssub_w sz
  end.

Definition smul_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => (Pconst (n1 * n2), LT_remove)
  | Some n, _ =>
    if (n == 0)%Z then (Pconst 0, LT_remove)
    else if (n == 1)%Z then (e2, LT_compose (LT_subi 0) (LT_subi 1))
    else (Papp2 (Omul Op_int) e1 e2, LT_id)
  | _, Some n =>
    if (n == 0)%Z then (Pconst 0, LT_remove)
    else if (n == 1)%Z then (e1, LT_compose (LT_subi 0) (LT_subi 0))
    else (Papp2 (Omul Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Omul Op_int) e1 e2, LT_id)
  end.

Definition smul_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 * n2), LT_map[:: LT_remove; LT_id])
  | Some n, _ =>
    if n == 0%R then (@wconst sz 0, LT_map[:: LT_remove; LT_id])
    else if n == 1%R then (e2, LT_compose (LT_subi 0) (LT_subi 1))
    else (Papp2 (Omul (Op_w sz)) (wconst n) e2, LT_remove) (* FIXME *)
          (*LT_map [:: LT_compose (LT_subi 0) (LT_map [:: LT_remove; LT_remove]) ; LT_id]*) 
  | _, Some n =>
    if n == 0%R then (@wconst sz 0, LT_map[:: LT_remove; LT_id])
    else if n == 1%R then (e1, LT_compose (LT_subi 0) (LT_subi 0))
    else (Papp2 (Omul (Op_w sz)) e1 (wconst n), LT_map [:: LT_id; LT_remove])
  | _, _ => (Papp2 (Omul (Op_w sz)) e1 e2, LT_id) (* FIXME *) 
  end.

Definition smul ty :=
  match ty with
  | Op_int => smul_int
  | Op_w sz => smul_w sz
  end.

Definition s_eq ty e1 e2 :=
  if eq_expr e1 e2 then (Pbool true, LT_remove)
  else
    match ty with
    | Op_int =>
      match is_const e1, is_const e2 with
      | Some i1, Some i2 => (Pbool (i1 == i2), LT_remove)
      | _, _             => (Papp2 (Oeq ty) e1 e2, LT_id)
      end
    | Op_w sz =>
      match is_wconst sz e1, is_wconst sz e2 with
      | Some i1, Some i2 => (Pbool (i1 == i2), LT_remove)
      | _, _             => (Papp2 (Oeq ty) e1 e2, LT_id)
      end
    end.

Definition sneq ty e1 e2 :=
  match is_bool (s_eq ty e1 e2).1 with
  | Some b => (Pbool (~~ b), LT_remove)
  | None      => (Papp2 (Oneq ty) e1 e2, LT_id)
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
  if eq_expr e1 e2 then (Pbool false, LT_remove)
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => (Pbool (n1 <? n2)%Z, LT_remove)
  | _      , _       => (Papp2 (Olt ty) e1 e2, LT_id)
  end.

Definition sle ty e1 e2 :=
  if eq_expr e1 e2 then (Pbool true, LT_remove)
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => (Pbool (n1 <=? n2)%Z, LT_remove)
  | _      , _       => (Papp2 (Ole ty) e1 e2, LT_id)
  end.

Definition sgt ty e1 e2 :=
  if eq_expr e1 e2 then (Pbool false, LT_remove)
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => (Pbool (n1 >? n2)%Z, LT_remove)
  | _      , _       => (Papp2 (Ogt ty) e1 e2, LT_id)
  end.

Definition sge ty e1 e2 :=
  if eq_expr e1 e2 then (Pbool true, LT_remove)
  else match is_cmp_const ty e1, is_cmp_const ty e2 with
  | Some n1, Some n2 => (Pbool (n1 >=? n2)%Z, LT_remove)
  | _      , _       => (Papp2 (Oge ty) e1 e2, LT_id)
  end.

Definition sbitw i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (z sz n1 n2), LT_map[:: LT_remove; LT_remove])
  | _, _ => (Papp2 (i sz) e1 e2, LT_id)
  end.

Definition soint i f e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 =>  (Pconst (f n1 n2), LT_remove)
  | _, _ => (Papp2 (i Cmp_int) e1 e2, LT_id)
  end.

Definition sbituw i (z: signedness -> ∀ sz, word sz → word sz → word sz) u sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 =>
    if n2 == 0%R then (Papp2 (i (Cmp_w u sz)) e1 e2, LT_id)
    else (wconst (z u sz n1 n2), LT_map[:: LT_remove; if u is Unsigned then LT_remove else LT_remove])
  | _, _ => (Papp2 (i (Cmp_w u sz)) e1 e2, LT_id)
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
  | Some n1, Some n2 => (wconst (z sz n1 n2), LT_map[:: LT_remove; LT_remove])
  | _, _ => (Papp2 (i sz) e1 e2, LT_id)
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
  match (mapM force_int es >>= sem_opN op) with
  | Ok (Vword sz w) => (Papp1 (Oword_of_int sz) (Pconst (wunsigned w)), LT_map[:: LT_remove; LT_remove])
  | _ => (PappN op es, LT_id)
  end.

Definition s_if t e e1 e2 :=
  match is_bool e with
  | Some b => if b then (e1, LT_compose (LT_subi 0) (LT_subi 1))
                   else (e2, LT_compose (LT_subi 0) (LT_subi 2))
  | None   => (Pif t e e1 e2, LT_id)
  end.

(* ** constant propagation
 * -------------------------------------------------------------------- *)

Variant const_v :=
  | Cbool of bool
  | Cint of Z
  | Cword sz `(word sz).

Definition const_v_beq (c1 c2: const_v) : bool :=
  match c1, c2 with
  | Cbool b1, Cbool b2 => b1 == b2
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
case => [ b1 | z1 | sz1 w1 ] [ b2 | z2 | sz2 w2] /=; try (constructor; congruence).
+ case: eqP => [ -> | ne ]; constructor; congruence.
+ case: eqP => [ -> | ne ]; constructor; congruence.
case: wsize_eq_dec => [ ? | ne ]; last (constructor; congruence).
subst => /=.
by apply:(iffP idP) => [ /eqP | [] ] ->.
Qed.

Definition const_v_eqMixin     := Equality.Mixin const_v_eq_axiom.
Canonical  const_v_eqType      := Eval hnf in EqType const_v const_v_eqMixin.

Local Notation cpm := (Mvar.t const_v).

Definition const v : (pexpr * leak_e_tr) :=
  match v with
  | Cbool b => (Pbool b, LT_remove)
  | Cint z  => (Pconst z, LT_remove)
  | Cword sz z => (wconst z, LT_seq [:: LT_remove; LT_remove])
  end.

Fixpoint const_prop_e (m:cpm) e : (pexpr * leak_e_tr) :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _
    => (e, LT_id)
  | Pvar  x       => if Mvar.get m x is Some n then (const n) else (e, LT_id)
  | Pglobal _     => (e, LT_id)
  | Pget  sz x e0  => let lte := (const_prop_e m e0) 
                      in (Pget sz x lte.1, LT_map [ :: lte.2; LT_id])
  | Pload sz x e0  => let lte := (const_prop_e m e0) in 
                      (Pload sz x lte.1, LT_map [:: lte.2; LT_id])
  | Papp1 o e0     => let lte := (const_prop_e m e0) in 
                      let ltop := (s_op1 o lte.1) in 
                      (ltop.1, LT_compose (LT_map [:: lte.2; LT_id]) ltop.2)
  | Papp2 o e1 e2 => let lte1 := (const_prop_e m e1) in
                     let lte2 := (const_prop_e m e2) in
                     let ltop := s_op2 o lte1.1 lte2.1 in
                     (ltop.1, LT_compose (LT_map [:: LT_map [:: lte1.2; lte2.2]; LT_id]) ltop.2)
  | PappN op es   =>
    let esk := map (const_prop_e m) es in
    let ek := s_opN op (unzip1 esk) in
    (ek.1, LT_compose (LT_map [:: LT_map (unzip2 esk); LT_id]) ek.2)
  | Pif t e0 e1 e2 => let lte0 := (const_prop_e m e0) in
                      let lte1 := (const_prop_e m e1) in
                      let lte2 := (const_prop_e m e2) in
                      let ltif := s_if t lte0.1 lte1.1 lte2.1 in
                      (ltif.1, LT_remove) (*FIXME*) (*LT_compose (LT_map [:: lte0.2; lte1.2; lte2.2]) ltif.2*)
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

Definition const_prop_rv (m:cpm) (rv:lval) : cpm * lval * leak_e_tr :=
  match rv with
  | Lnone _ _    => (m, rv, LT_id)
  | Lvar  x      => (Mvar.remove m x, rv, LT_id)
  | Lmem  sz x e => let lte := const_prop_e m e in 
                    (m, Lmem sz x lte.1, LT_map [:: lte.2; LT_id])
  | Laset sz x e => let lte := const_prop_e m e in 
                    (Mvar.remove m x, Laset sz x lte.1, LT_map [:: lte.2; LT_id])
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals * seq leak_e_tr :=
  match rvs with
  | [::] => (m, [::], [::])
  | rv::rvs =>
    let: (m,rv, lt)  := const_prop_rv m rv in
    let: (m,rvs, lts) := const_prop_rvs m rvs in
    (m, rv::rvs, (lt :: lts))
  end.

Definition wsize_of_stype (ty: stype) : wsize :=
  if ty is sword sz then sz else U64.

Definition add_cpm (m:cpm) (rv:lval) tag ty e :=
  if rv is Lvar x then
    if tag is AT_inline then
      match e with
      | Pbool b  => Mvar.set m x (Cbool b)
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

  Variable const_prop_i : cpm -> instr -> cpm * cmd * leak_i_tr.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd * leak_c_tr :=
    match c with
    | [::] => (m, [::], [::])
    | i::c =>
      let: (m,ic, lti) := const_prop_i m i in
      let: (m, c, ltc) := const_prop m c in
      (m, ic ++ c, (lti :: ltc))
    end.

End CMD. 

Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd * leak_i_tr :=
  match ir with
  | Cassgn x tag ty e =>
    let (e, lt) := const_prop_e m e in
    let: (m,x, ltx) := const_prop_rv m x in
    let m := add_cpm m x tag ty e in
    (m, [:: MkI ii (Cassgn x tag ty e)], LT_ile (LT_map (lt :: [:: ltx])))

  | Copn xs t o es =>
    (* TODO: Improve this *)
    let es := map (const_prop_e m) es in
    let: (m,xs, lts) := const_prop_rvs m xs in
    (m, [:: MkI ii (Copn xs t o (unzip1 es)) ], 
     LT_ile (LT_map [:: LT_map (unzip2 es) ; LT_id; LT_map lts]))
            
  | Cif b c1 c2 =>
    let (b, ltb) := const_prop_e m b in
    match is_bool b with
    | Some b =>
      if b then let: (v1, cm1, ltc1) := const_prop const_prop_i m c1 in 
                     (v1, cm1, LT_icond_eval true ltc1)
           else let: (v2, cm2, ltc2) := const_prop const_prop_i m c2 in 
                     (v2, cm2, LT_icond_eval false ltc2) 
    | None =>
      let: (m1,c1,lt1) := const_prop const_prop_i m c1 in
      let: (m2,c2,lt2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ], LT_icond ltb lt1 lt2)
    end

  | Cfor x (dir, e1, e2) c =>
    let (e1, lte1) := const_prop_e m e1 in
    let (e2, lte2) := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let: (_,c, ltc) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ], LT_ifor (LT_map [:: lte1; lte2]) ltc)

  | Cwhile a c e c' =>
    let m := remove_cpm m (write_i ir) in
    let: (m',c, ltc) := const_prop const_prop_i m c in
    let (e, lte) := const_prop_e m' e in
    let: (_,c', ltc') := const_prop const_prop_i m' c' in
    if is_bool e == Some false then (m', c, LT_icond_eval false ltc) 
    else (m', [:: MkI ii (Cwhile a c e c')], LT_iwhile ltc lte ltc')

  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let: (m,xs,lt) := const_prop_rvs m xs in
    (m, [:: MkI ii (Ccall fi xs f (unzip1 es)) ], (LT_icall f (LT_map (unzip2 es)) (LT_map lt)))
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd * leak_i_tr :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,tin,p,c,tout,r) := f in
  let: (_, c, lt) := const_prop const_prop_i empty_cpm c in
  (MkFun ii tin p c tout r, lt).

Definition const_prop_prog (p: prog) : (prog * leak_f_tr) :=
  let fs := map_prog_leak const_prop_fun (p_funcs p) in
  ({| p_globs := p_globs p; p_funcs := fs.1 |}, fs.2).


