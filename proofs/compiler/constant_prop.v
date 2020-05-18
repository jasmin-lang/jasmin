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
Require Import dead_code.
Require Export low_memory.
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

Inductive leak_tr :=
| LT_id
| LT_remove
| LT_subi : Z -> leak_tr
| LT_seq : seq leak_tr -> leak_tr
| LT_compose: leak_tr -> leak_tr -> leak_tr.

Inductive leak_e_tree :=
| LEmpty : leak_e_tree
| LIdx : Z -> leak_e_tree
| LAdr : pointer -> leak_e_tree
| LSub: (seq leak_e_tree) -> leak_e_tree.

Fixpoint get_nth (ls : seq leak_e_tree) (i : Z) : leak_e_tree :=
match ls with 
 | [::] => LEmpty 
 | x :: xs => if (i == 0) then x else get_nth xs (i-1)
end.

Fixpoint leak_F (lt : leak_tr) (l : leak_e_tree) : leak_e_tree := 
  match lt, l with
  | LT_seq lts, LSub xs => LSub (map2 leak_F lts xs)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi i, LSub xs => get_nth xs i
  | LT_compose lt1 lt2, _ => leak_F lt2 (leak_F lt1 l)
  | _, _ => LEmpty
  end.

Section LEST_TO_LES.

Variable (lest_to_les : leak_e_tree -> leakages_e).

Definition lests_to_les (l : seq leak_e_tree) : leakages_e := 
    flatten (map lest_to_les l).

End LEST_TO_LES.

Fixpoint lest_to_les (les : leak_e_tree) : leakages_e := 
  match les with 
  | LEmpty => [::]
  | LIdx i => [:: LeakIdx i]
  | LAdr p => [:: LeakAdr p]
  | LSub les => lests_to_les lest_to_les les
  end.

Definition sword_of_int sz (e: pexpr) :=
  (Papp1 (Oword_of_int sz) e, LT_id).

Definition sint_of_word sz (e: pexpr) :=
  if is_wconst sz e is Some w
  then (Pconst (wunsigned w), LT_remove)
  else (Papp1 (Oint_of_word sz) e, LT_id).

Definition ssign_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (sign_extend sz w))), LT_remove)
  else (Papp1 (Osignext sz sz') e, LT_id).

Definition szero_extend sz sz' (e: pexpr) :=
  if is_wconst sz' e is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (zero_extend sz w))), LT_remove)
  else (Papp1 (Ozeroext sz sz') e, LT_id).

Definition snot_bool (e:pexpr) : (pexpr * leak_tr) :=
  match e with
  | Pbool b      => (Pbool (negb b), LT_remove)
  | Papp1 Onot e0 => (e0, LT_id)
  | _            => (Papp1 Onot e, LT_id)
  end.

Definition snot_w (sz: wsize) (e:pexpr) : (pexpr*leak_tr) :=
  match is_wconst sz e with
  | Some n => (wconst (wnot n),LT_remove)
  | None   => (Papp1 (Olnot sz) e, LT_id)
  end.

Definition sneg_int (e: pexpr) : (pexpr*leak_tr) :=
  match e with
  | Pconst z => (Pconst (- z), LT_remove)
  | Papp1 (Oneg Op_int) e' => (e', LT_id)
  | _ => (Papp1 (Oneg Op_int) e, LT_id)
  end.

Definition sneg_w (sz: wsize) (e:pexpr) : (pexpr*leak_tr) :=
  match is_wconst sz e with
  | Some n => (wconst (- n)%R, LT_remove)
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
  | Some b, _ => if b then (e2, LT_subi 1) else (Pbool false, LT_remove)
  | _, Some b => if b then (e1, LT_subi 0) else (Pbool false, LT_remove)
  | _, _      => (Papp2 Oand e1 e2, LT_id)
  end.

Definition sor e1 e2 :=
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then (Pbool true, LT_remove) else (e2, LT_subi 1)
  | _, Some b => if b then (Pbool true, LT_remove) else (e1, LT_subi 0)
  | _, _       => (Papp2 Oor e1 e2, LT_id)
  end.

(* ------------------------------------------------------------------------ *)

Definition sadd_int e1 e2 :=
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => (Pconst (n1 + n2), LT_remove)
  | Some n, _ =>
    if (n == 0)%Z then (e2, LT_subi 1) 
                  else (Papp2 (Oadd Op_int) e1 e2, LT_id)
  | _, Some n =>
    if (n == 0)%Z then (e1, LT_subi 0) 
                  else (Papp2 (Oadd Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Oadd Op_int) e1 e2, LT_id)
  end.

Definition sadd_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 + n2), LT_remove)
  | Some n, _ => if n == 0%R then (e2, LT_subi 1) 
                             else (Papp2 (Oadd (Op_w sz)) e1 e2, LT_id)
  | _, Some n => if n == 0%R then (e1, LT_subi 0) 
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
    if (n == 0)%Z then (e1, LT_subi 0) 
                  else (Papp2 (Osub Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Osub Op_int) e1 e2, LT_id)
  end.

Definition ssub_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 - n2), LT_remove)
  | _, Some n => if n == 0%R then (e1, LT_subi 0) 
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
    else if (n == 1)%Z then (e2, LT_subi 1)
    else (Papp2 (Omul Op_int) e1 e2, LT_id)
  | _, Some n =>
    if (n == 0)%Z then (Pconst 0, LT_remove)
    else if (n == 1)%Z then (e1, LT_subi 0)
    else (Papp2 (Omul Op_int) e1 e2, LT_id)
  | _, _ => (Papp2 (Omul Op_int) e1 e2, LT_id)
  end.

Definition smul_w sz e1 e2 :=
  match is_wconst sz e1, is_wconst sz e2 with
  | Some n1, Some n2 => (wconst (n1 * n2), LT_remove)
  | Some n, _ =>
    if n == 0%R then (@wconst sz 0, LT_remove)
    else if n == 1%R then (e2, LT_subi 1)
    else (Papp2 (Omul (Op_w sz)) (wconst n) e2, LT_seq [:: LT_remove; LT_id])
  | _, Some n =>
    if n == 0%R then (@wconst sz 0, LT_remove)
    else if n == 1%R then (e1, LT_subi 0)
    else (Papp2 (Omul (Op_w sz)) e1 (wconst n), LT_seq [:: LT_id; LT_remove])
  | _, _ => (Papp2 (Omul (Op_w sz)) e1 e2, LT_id)
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
  | Some n1, Some n2 => (wconst (z sz n1 n2), LT_remove)
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
    else (wconst (z u sz n1 n2), LT_remove)
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
  | Some n1, Some n2 => (wconst (z sz n1 n2), LT_remove)
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

(*Definition force_int e :=
  if e is Pconst z then ok (Vint z) else type_error.*)

Definition force_int e :=
  match e with 
  |(Pconst z) => ok (Vint z)
  | _ => type_error
  end.

Definition s_opN op es :=
  match (mapM force_int es >>= sem_opN op) with
  | Ok (Vword sz w) => (Papp1 (Oword_of_int sz) (Pconst (wunsigned w)), LT_remove)
  | _ => (PappN op es, LT_id)
  end.

Definition s_if t e e1 e2 :=
  match is_bool e with
  | Some b => if b then (e1, (LT_subi 1))
                   else (e2, (LT_subi 2))
  | None   => (Pif t e e1 e2, LT_id)
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

Fixpoint const_prop_e (m:cpm) e : (pexpr * leak_tr) :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _
    => (e, LT_id)
  | Pvar  x       => if Mvar.get m x is Some n then (const n, LT_remove) else (e, LT_id)
  | Pglobal _     => (e, LT_id)
  | Pget  sz x e0  => let lte := (const_prop_e m e0) 
                      in (Pget sz x lte.1, LT_seq [ :: lte.2; LT_id])
  | Pload sz x e0  => let lte := (const_prop_e m e0) in 
                      (Pload sz x lte.1, LT_seq [:: lte.2; LT_id])
  | Papp1 o e0     => let lte := (const_prop_e m e0) in 
                      let ltop := (s_op1 o lte.1) in 
                      (ltop.1, LT_compose lte.2 ltop.2)
  | Papp2 o e1 e2 => let lte1 := (const_prop_e m e1) in
                     let lte2 := (const_prop_e m e2) in
                     let ltop := s_op2 o lte1.1 lte2.1 in
                     (ltop.1, LT_compose (LT_seq [:: lte1.2; lte2.2]) ltop.2)
  | PappN op es   => s_opN op es
  | Pif t e0 e1 e2 => let lte0 := (const_prop_e m e0) in
                      let lte1 := (const_prop_e m e1) in
                      let lte2 := (const_prop_e m e2) in
                      let ltif := s_if t lte0.1 lte1.1 lte2.1 in
                      (ltif.1, LT_compose (LT_seq [:: lte0.2 ; lte1.2; lte2.2]) ltif.2)
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

Definition const_prop_rv (m:cpm) (rv:lval) : cpm * lval * leak_tr :=
  match rv with
  | Lnone _ _    => (m, rv, LT_id)
  | Lvar  x      => (Mvar.remove m x, rv, LT_id)
  | Lmem  sz x e => let lte := const_prop_e m e in 
                    (m, Lmem sz x lte.1, LT_seq [:: lte.2; LT_id])
  | Laset sz x e => let lte := const_prop_e m e in 
                    (Mvar.remove m x, Laset sz x lte.1, LT_seq [:: lte.2; LT_id])
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals * leak_tr :=
  match rvs with
  | [::] => (m, [::], LT_id)
  | rv::rvs =>
    let: (m,rv, lt)  := const_prop_rv m rv in
    let: (m,rvs, lts) := const_prop_rvs m rvs in
    (m, rv::rvs, LT_compose lt lts)
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


Section SEM_PEXPR_E.

Context (gd: glob_decls).

Fixpoint sem_pexpr_e (s:estate) (e : pexpr) : exec (value * leak_e_tree) :=
  match e with
  | Pconst z => ok (Vint z, LEmpty)
  | Pbool b  => ok (Vbool b, LEmpty)
  | Parr_init n => ok (Varr (WArray.empty n), LEmpty)
  | Pvar x => Let v := get_var s.(evm) x in 
              ok (v, LEmpty)
  | Pglobal g => Let v := get_global gd g in 
                 ok (v, LEmpty)
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let vl := sem_pexpr_e s e in 
      Let i := to_int vl.1 in 
      Let w := WArray.get ws t i in
      ok ((Vword w), LSub [ :: vl.2 ; (LIdx i)])
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let vl2 := sem_pexpr_e s e in 
    Let w2 := to_pointer vl2.1 in
    let adr := (w1 + w2)%R in 
    Let w  := read_mem s.(emem) adr sz in
    ok (@to_val (sword sz) w, LSub [ :: vl2.2;  (LAdr adr)])
  | Papp1 o e1 =>
    Let vl := sem_pexpr_e s e1 in
    Let v := sem_sop1 o vl.1 in 
    ok (v, vl.2)
  | Papp2 o e1 e2 =>
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v := sem_sop2 o vl1.1 vl2.1 in
    ok (v, LSub [:: vl1.2; vl2.2])
  | PappN op es =>
    Let vs := mapM (sem_pexpr_e s) es in
    Let v := sem_opN op (unzip1 vs) in
    ok (v, LSub (unzip2 vs))
  | Pif t e e1 e2 =>
    Let vl := sem_pexpr_e s e in
    Let b := to_bool vl.1in
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v1 := truncate_val t vl1.1 in
    Let v2 := truncate_val t vl2.1 in
    ok (if b then v1 else v2, LSub [:: vl.2 ; vl1.2; vl2.2])
  end.

Definition sem_pexprs_e s es :=
  Let vls := mapM (sem_pexpr_e s) es in
  ok (unzip1 vls, LSub (unzip2 vls)).

Definition write_lval_e (l:lval) (v:value) (s:estate) : exec (estate * leak_e_tree) :=
  match l with
  | Lnone _ ty => Let x := write_none s ty v in ok (x, LEmpty)
  | Lvar x => Let v' := write_var x v s in ok(v', LEmpty)
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let vl := sem_pexpr_e s e in 
    Let ve := to_pointer vl.1 in
    let p := (vx + ve)%R in
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok ({| emem := m;  evm := s.(evm) |}, LSub [:: vl.2; (LAdr p)])
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let vl := sem_pexpr_e s i in 
    Let i := to_int vl.1 in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |}, LSub [:: vl.2; (LIdx i)])
  end.

Definition write_lvals_e (s:estate) xs vs :=
   fold2 ErrType (fun l v sl => Let sl' := write_lval_e l v sl.1 in ok (sl'.1, LSub [:: sl.2 ; sl'.2]))
      xs vs (s, LEmpty).


End SEM_PEXPR_E.

Section Sem_e_Leakages_proof.

Context (gd: glob_decls).

Context (s:estate).

Definition flatten_exec (p : exec (value * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Definition flatten_estate (p : exec (estate * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Definition flatten_range (p : exec (seq Z * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Fixpoint vlest_to_vles (p : seq (value * leak_e_tree)) := 
match p with 
| [::] => ([::])
| x :: xl => ((x.1, lest_to_les x.2) :: vlest_to_vles xl)
end.

Definition flatten_execs (p : exec (seq (value * leak_e_tree))) := 
Let v := p in 
ok (vlest_to_vles v).


Let P e : Prop := forall v, sem_pexpr_e gd s e = ok v -> 
            sem_pexpr gd s e = ok (v.1, lest_to_les v.2).

Let Q es : Prop := forall vs, mapM (sem_pexpr_e gd s) es = ok vs ->
           mapM (sem_pexpr gd s) es = ok (zip (unzip1 vs) (map (lest_to_les) (unzip2 vs))).

Let Q'' es : Prop := forall vs, sem_pexprs_e gd s es = ok vs ->
           sem_pexprs gd s es = ok (vs.1, lest_to_les vs.2).

  Lemma sem_pexpr_e_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
  apply: pexprs_ind_pair ; split ; subst P Q => //=.
  + move=> vs He. by case: He => <- /=.
  + move=> e H es Hm vs. t_xrbindP.
    move=> [yv yl] Hs ho Hm' <- /=. move: (H (yv, yl) Hs) => -> /=.
    by move: (Hm ho Hm') => -> /=.
  + move=> z [v l] He /=. by case: He => -> <- /=.
  + move=> b [v l] He /=. by case: He => -> <- /=.
  + move=> z [v l] He /=. by case: He => -> <- /=.
  + t_xrbindP. move=> v [hv hl] y -> He /=. by case: He => -> <- /=.
  + t_xrbindP. move=> h [hv hl] y -> He /=. by case: He => -> <- /=.
  + move=> sz x e H [v l] /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] Hs z Hi w Ha <- <- /=.
    move: (H (yv, yl) Hs) => -> /=. rewrite Hi /=. rewrite Hg /=.
    rewrite Ha /=. rewrite /lests_to_les /=. by rewrite cats1.
  + move=> sz x e H [v l] /=. t_xrbindP.
    move=> y h -> /= -> /= [hv hl] Hs h' Hp' /= w Hr He <- /=.
    move: (H (hv, hl) Hs) => -> /=. rewrite Hp' /=. rewrite Hr /=.
    rewrite He /=. rewrite /lests_to_les /=.
    by rewrite cats1.
  + move=> op e Hs. t_xrbindP.
    move=> [hv hl] [yv yl] Hse h1 Hop He. move: (Hs (yv, yl) Hse) => -> /=.
    rewrite Hop /=. case: He => -> <- /=. by rewrite /lests_to_les /=.
  + move=> op e1 H1 e2 H2 [v l]. t_xrbindP.
    move=> [yv yl] Hs [hv hl] Hs' v' Hop <- <- /=.
    move: (H1 (yv, yl) Hs) => -> /=. move: (H2 (hv, hl) Hs') => -> /=.
    rewrite Hop /=. rewrite /lests_to_les /=. by rewrite cats0.
  + move=> op es Hes. t_xrbindP. move=> [yv yl] ys Hm. move=> h1 Ho.
    move=> [] Hh Hl. move: (Hes ys Hm) => Hm'. rewrite Hm' /=.
    assert ((unzip1
        (zip (unzip1 ys) [seq lest_to_les i | i <- unzip2 ys])) = unzip1 ys).
    apply unzip1_zip. elim: (ys) => //= x s. rewrite H /=. rewrite Ho /=.
    assert ((unzip2
       (zip (unzip1 ys)
          [seq lest_to_les i | i <- unzip2 ys])) = [seq lest_to_les i | i <- unzip2 ys]).
    apply unzip2_zip. elim: (ys) => //= x s. rewrite H0 Hh -Hl /=. by rewrite /lests_to_les /=. 
  move=> t e H e1 H1 e2 H2 [v l]. t_xrbindP.
  move=> [yv yl] Hs b Hb [hv hl] He1 [hv' hl'] He2 he1 Hhe1 he2 Hhe2 He <- /=.
  move: (H (yv, yl) Hs) => -> /=.
  move: (H1 (hv, hl) He1) => -> /=.
  move: (H2 (hv', hl') He2) => -> /=.
  rewrite Hb /=. rewrite Hhe1 /=. rewrite Hhe2 /=. rewrite He /=.
  rewrite /lests_to_les /=. by rewrite cats0.
  Qed.

  Lemma sem_pexpr_e_sim' : (∀ e, P e) ∧ (∀ es, Q'' es).
  Proof.
  rewrite /Q''. rewrite /sem_pexprs. rewrite /sem_pexprs_e.
  move:  sem_pexpr_e_sim => [] H1 H2. rewrite /Q in H2.
  split; auto. move=> es vs. t_xrbindP => y Hm <-. move: (H2 es y) => H1'. 
  move: (H1' Hm) => H. rewrite H /=.
  assert ((unzip1
     (zip (unzip1 y) [seq lest_to_les i | i <- unzip2 y])) = unzip1 y).
  apply unzip1_zip. elim: (y) => //= x s. rewrite H0 /=.
  assert ((unzip2
       (zip (unzip1 y)
          [seq lest_to_les i | i <- unzip2 y])) = [seq lest_to_les i | i <- unzip2 y]).
    apply unzip2_zip. elim: (y) => //= x s. by rewrite H3 /lests_to_les /=.
  Qed.

End Sem_e_Leakages_proof.

Definition const_prop_e_esP_sem_pexpr_e gd s e v:=
  (@sem_pexpr_e_sim gd s).1 e v.

Definition const_prop_e_esP_sem_pexprs_e gd s es v:=
  (@sem_pexpr_e_sim gd s).2 es v.

Definition const_prop_e_esP_sem_pexprs_e' gd s es v:=
  (@sem_pexpr_e_sim' gd s).2 es v.

  Lemma sem_pexpr_e_to_sem_pexpr gd s e v l':
  sem_pexpr gd s e = ok (v, l') ->
  exists l, l' = lest_to_les l /\ sem_pexpr_e gd s e = ok (v, l).
  Proof.
  elim: e v l'.
  + move=> z v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> b v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> n v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> x v l'. rewrite /sem_pexpr. t_xrbindP.
    move=> y Hg <- <- /=. rewrite Hg /=. exists LEmpty. split; auto.
  + move=> g v l. rewrite /sem_pexpr. t_xrbindP.
    move=> y Hg <- <- /=. rewrite Hg /=. exists LEmpty. split; auto.
  + move=> sz x e He v l' /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] He' z Hi w Ha Hv Hl /=.
    move: (He yv yl He') => [] l [] Hs Hs'. rewrite Hs' /=.
    rewrite Hg /=. rewrite Hi /=. rewrite Ha /=. 
    exists (LSub [:: l; (LIdx z)]). split. rewrite -Hl /=.
    rewrite Hs /=. rewrite /lests_to_les /=. by rewrite cats1.
    by rewrite -Hv.
  + move=> sz x e He /=. t_xrbindP.
    move=> v l y v1 Hg Hp [yv yl] He' h6 Hp' h8 Hr Hv Hl /=.
    move: (He yv yl He') => [] l' [] Hs Hs'. rewrite Hg /=.
    rewrite Hp /=. rewrite Hs' /=. rewrite Hp' /=. rewrite Hr /=.
    exists (LSub [:: l' ; (LAdr (y + h6))]). split. rewrite -Hl /=.
    rewrite /lests_to_les /=. rewrite -Hs /=. by rewrite cats1.
    by rewrite -Hv.
  + move=> op e He /=. t_xrbindP.
    move=> v l [yv yl] He' h2 Ho Hv Hl.
    move: (He yv yl He') => [] l' [] Hs Hs'. rewrite Hs' /=.
    rewrite Ho /=. exists l'. split.
    rewrite -Hl /=. rewrite Hs /=. by rewrite /lests_to_les /=.
    by rewrite Hv.
  + move=> op e1 He1 e2 He2 /=. t_xrbindP.
    move=> v l' [yv yl] He1' [yv' yl'] He2' v' Ho Hv Hl /=.
    move: (He1 yv yl He1') => [] l1 [] Hs1 Hs1'. rewrite Hs1' /=.
    move: (He2 yv' yl' He2') => [] l2 [] Hs2 Hs2'. rewrite Hs2' /=.
    exists (LSub [:: l1; l2]). split.
    rewrite -Hl /=. rewrite Hs1 Hs2 /=. rewrite /lests_to_les /=. by rewrite cats0.
    rewrite Ho /=. by rewrite Hv.
  + move=> op es He /=. t_xrbindP. move: (const_prop_e_esP_sem_pexprs_e) => H h1 h0 y0 Hm.
    move: (H gd s es) => H1. move=> h2 Ho <- /= <- /=.
    move: (const_prop_e_esP_sem_pexpr_e)=> H2. 
    admit.
  + move=> t e He e1 He1 e2 He2 /=. t_xrbindP.
    move=> h h0 [yv yl] He' b Hb [yv' yl'] He1' [yv'' yl''] He2' h8 Ht h9 Ht' Hv Hl.
    move: (He yv yl He') => [] x [] Hs Hs'. rewrite Hs' /=.
    rewrite Hb /=. move: (He1 yv' yl' He1') => [] x0 [] Hs1 Hs1'. rewrite Hs1' /=.
    move: (He2 yv'' yl'' He2') => [] x0' [] Hs2 Hs2'. rewrite Hs2' /=. 
    rewrite Ht /=. rewrite Ht' /=. rewrite Hv /=.
    exists (LSub [:: x; x0; x0']). split. rewrite -Hl /=. rewrite Hs Hs1 Hs2 /=.
    rewrite /lests_to_les /=. by rewrite cats0. auto.
  Admitted.


  Lemma write_lval_cp gd s1 x v s2 l:
  write_lval_e gd x v s1 = ok (s2, l) ->
  write_lval gd x v s1 = ok (s2, lest_to_les l).
  Proof.
  case : x => /=.
  - move=> _ ty. rewrite /write_none. t_xrbindP.
    move=> y H <- <- /=. by rewrite H /=.
  - move=> x. rewrite /write_var. t_xrbindP.
    move=> y h Hs Hy He <- /=. rewrite Hs /=. rewrite -Hy in He.
    by rewrite -He /=.
  - move=> sz x e. t_xrbindP.
    move=> y h -> /= -> /= [v' l'] He h4 Hw h8 Hw' m Hm <- <- /=.
    move: (const_prop_e_esP_sem_pexpr_e). move=> H.
    move: (H gd s1 e (v', l') He) => -> /=. rewrite Hw /=.
    rewrite Hw' /=. rewrite Hm /=. rewrite /lests_to_les /=.
    by rewrite cats1.
  - move=> sz x e /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] Hs z Hi w Hw a Ha h6 Hs' <- <- /=.
    rewrite Hg /=. move: (const_prop_e_esP_sem_pexpr_e). move=> H.
    move: (H gd s1 e (yv, yl) Hs) => -> /=.
    rewrite Hi /=. rewrite Hw /=. rewrite Ha /=. rewrite Hs' /=.
    rewrite /lests_to_les /=. by rewrite cats1.
  Qed.

  Lemma write_lvals_cp gd s1 xs vs s2 l:
  write_lvals_e gd s1 xs vs = ok (s2, l) ->
  write_lvals gd s1 xs vs = ok (s2, lest_to_les l).
  Proof.
  rewrite /write_lvals. rewrite /write_lvals_e.
  elim: xs vs s1 [::] l s2 => [|x xs Hrec] [|v vs] s1 lw0 lw s2 //=.
  + by move=> [] <- <- /=.
  t_xrbindP => ? [s lw1] /write_lval_cp -> <- /=. move=> H.
  Admitted.

Section CMD.

Inductive leak_i_tree :=
| LTempty : leak_i_tree  
| LTassgn : leak_e_tree -> leak_i_tree
| LTopn : leak_e_tree -> leak_i_tree
| LTcond : leak_e_tree -> bool -> leak_i_tree -> leak_i_tree
| LTwhile_true : leak_i_tree -> leak_e_tree -> leak_i_tree -> leak_i_tree -> leak_i_tree
| LTwhile_false : leak_i_tree -> leak_e_tree -> leak_i_tree
| LTfor : leak_e_tree -> seq (seq leak_i_tree) -> leak_i_tree
| LTcall : leak_e_tree -> (funname * leak_i_tree) -> leak_e_tree -> leak_i_tree
| LTSub : seq leak_i_tree -> leak_i_tree.


Inductive leak_i_tr :=
| LT_iremove : leak_i_tr
| LT_ikeep : leak_i_tr
| LT_ile : leak_tr -> leak_i_tr
| LT_ileli : leak_tr -> leak_i_tr -> leak_i_tr
| LT_iwhile : leak_i_tr -> leak_tr -> leak_i_tr -> leak_i_tr
| LT_ifor : leak_tr -> seq (seq leak_i_tr) -> leak_i_tr
| LT_icall : leak_tr -> leak_i_tr -> leak_tr -> leak_i_tr
| LT_iseq : seq leak_i_tr -> leak_i_tr.

Section LEAK_I.
  
  Variable leak_I : leak_i_tr -> leak_i_tree -> leak_i_tree.

  Definition leak_Is (lts : seq leak_i_tr) (ls : seq leak_i_tree) : seq leak_i_tree :=
    (map2b leak_I lts ls).

  Definition leak_Iss (ltss : seq (seq leak_i_tr)) (ls : seq (seq leak_i_tree)) : seq (seq leak_i_tree) :=
    (map2b leak_Is ltss ls).

End LEAK_I.

Fixpoint leak_I (lt : leak_i_tr) (l : leak_i_tree) : leak_i_tree :=
  match lt, l with
  | LT_iremove, _ => LTempty
  | LT_ikeep, _ => l
  | LT_iseq lts, LTSub ls => LTSub (map2b leak_I lts ls)
  | LT_ile lte, LTassgn le => LTassgn (leak_F lte le)
  | LT_ile lte, LTopn le => LTopn (leak_F lte le)
  | LT_ileli lte lti, LTcond le b li => LTcond (leak_F lte le) b (leak_I lti li)
  | LT_iwhile lti lte lti', LTwhile_true li le li' lw => LTwhile_true (leak_I lti li)
                                                                      (leak_F lte le)
                                                                      (leak_I lti' li')
                                                                      (leak_I lt lw)
  | LT_iwhile lti lte lti', LTwhile_false li le => LTwhile_false (leak_I lti li)
                                                                 (leak_F lte le)
  | LT_ifor lte lti, LTfor le li => LTfor (leak_F lte le)
                                          (leak_Iss leak_I lti li)
  | LT_icall lte lti lte', LTcall le (f, li) le' => LTcall (leak_F lte le)
                                                             (f, (leak_I lti li))
                                                             (leak_F lte' le')
  | _, _ => LTempty
 end.


Section LIT_TO_LI.

Variable (lit_to_li : leak_i_tree -> seq leakage_i).

Definition lits_to_lis (l : seq leak_i_tree) : seq leakage_i := 
  flatten (map lit_to_li l).

Definition litss_to_liss (ls : seq (seq leak_i_tree)) : seq (seq leakage_i) :=
  map lits_to_lis ls.

End LIT_TO_LI.

Variable l0 : leakage_i.

Fixpoint lit_to_li (lis : leak_i_tree) : seq leakage_i :=
 match lis with 
 | LTempty => [::]
 | LTassgn le => [:: (Lassgn (lest_to_les le))]
 | LTopn le => [:: (Lopn (lest_to_les le))]
 | LTcond le b li => [:: (Lcond (lest_to_les le) b (lit_to_li li))]
 | LTwhile_true li le li' li'' => [:: (Lwhile_true (lit_to_li li)
                                                   (lest_to_les le)
                                                   (lit_to_li li')
                                                   (head l0 (lit_to_li li'')))]
 | LTwhile_false li le => [:: (Lwhile_false (lit_to_li li)
                                             (lest_to_les le))]
 | LTfor le li => [:: (Lfor (lest_to_les le)
                            (litss_to_liss lit_to_li li))]
 | LTcall le (f, li) le' => [:: (Lcall (lest_to_les le)
                                        (f, (lit_to_li li))
                                        (lest_to_les le'))]
 | LTSub lis => lits_to_lis lit_to_li lis
 end.


  Variable const_prop_i : cpm -> instr -> cpm * cmd * leak_i_tr.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd * leak_i_tr :=
    match c with
    | [::] => (m, [::], LT_iremove)
    | i::c =>
      let: (m,ic, lti) := const_prop_i m i in
      let: (m, c, ltc) := const_prop m c in
      (m, ic ++ c, LT_iseq [:: lti; ltc])
    end.

End CMD.

Section SEM_I.
Variable P:prog.
Notation gd := (p_globs P).

Definition sem_range_e (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let vl1 := sem_pexpr_e gd s pe1 in 
  Let i1 := to_int vl1.1 in 
  Let vl2 := sem_pexpr_e gd s pe2 in 
  Let i2 := to_int vl2.1 in
  ok (wrange d i1 i2, LSub [:: vl1.2 ; vl2.2]).

Definition sem_sopn_e gd o m lvs args := 
  Let vas := sem_pexprs_e gd m args in
  Let vs := exec_sopn o vas.1 in 
  Let ml := write_lvals_e gd m lvs vs in
  ok (ml.1, LSub [ :: vas.2 ; ml.2]).


Inductive sem_c_i : estate -> cmd -> leak_i_tree -> estate -> Prop :=
| Eskip_i s :
    sem_c_i s [::] LTempty s

| Eseq_i s1 s2 s3 i c li lc :
    sem_I_i s1 i li s2 -> sem_c_i s2 c lc s3 -> sem_c_i s1 (i::c) (LTSub [:: li ; lc]) s3

with sem_I_i : estate -> instr -> leak_i_tree -> estate -> Prop :=
| EmkI_i ii i s1 s2 li:
    sem_i_i s1 i li s2 ->
    sem_I_i s1 (MkI ii i) li s2

with sem_i_i : estate -> instr_r -> leak_i_tree -> estate -> Prop :=
| Eassgn_i s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr_e gd s1 e = ok (v,l1)  ->
    truncate_val ty v = ok v' →
    write_lval_e gd x v' s1 = ok (s2, l2) ->
    sem_i_i s1 (Cassgn x tag ty e) (LTassgn (LSub [:: l1 ; l2])) s2

| Eopn_i s1 s2 t o xs es lo:
    sem_sopn_e gd o s1 xs es = ok (s2, lo) ->
    sem_i_i s1 (Copn xs t o es) (LTopn lo) s2

| Eif_true_i s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool true, le) ->
    sem_c_i s1 c1 lc s2 ->
    sem_i_i s1 (Cif e c1 c2) (LTcond le true lc) s2

| Eif_false_i s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool false, le) ->
    sem_c_i s1 c2 lc s2 ->
    sem_i_i s1 (Cif e c1 c2) (LTcond le false lc) s2

| Ewhile_true_i s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem_c_i s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool true, le) ->
    sem_c_i s2 c' lc' s3 ->
    sem_i_i s3 (Cwhile a c e c') lw s4 ->
    sem_i_i s1 (Cwhile a c e c') (LTwhile_true lc le lc' lw) s4

| Ewhile_false_i s1 s2 a c e c' lc le:
    sem_c_i s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool false, le) ->
    sem_i_i s1 (Cwhile a c e c') (LTwhile_false lc le) s2

| Efor_i s1 s2 (i:var_i) r c wr lr lf:
    sem_range_e s1 r = ok (wr, lr) ->
    sem_for_i i wr s1 c lf s2 ->
    sem_i_i s1 (Cfor i r c) (LTfor lr lf) s2

| Ecall_i s1 m2 s2 ii xs f args vargs vs l1 lf l2:
    sem_pexprs_e gd s1 args = ok (vargs, l1) ->
         sem_call_i s1.(emem) f vargs lf m2 vs ->
    write_lvals_e gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i_i s1 (Ccall ii xs f args) (LTcall l1 lf l2) s2

with sem_for_i : var_i -> seq Z -> estate -> cmd -> seq (seq leak_i_tree) -> estate -> Prop :=
| EForDone_i s i c :
    sem_for_i i [::] s c [::] s

| EForOne_i s1 s1' s2 s3 i w ws c lc lw :
    write_var i (Vint w) s1 = ok s1' ->
    sem_c_i s1' c lc s2 ->
    sem_for_i i ws s2 c lw s3 ->
    sem_for_i i (w :: ws) s1 c ([::lc] :: lw) s3

with sem_call_i : Memory.mem -> funname -> seq value -> (funname * leak_i_tree) -> Memory.mem -> seq value -> Prop :=
| EcallRun_i m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem_c_i s1 f.(f_body) lc (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call_i m1 fn vargs' (fn, lc) m2 vres'.

End SEM_I.

Section SEM_IND_I.

  Variable P:prog.
  Notation gd := (p_globs P).

  Variables
    (Pci  : estate -> cmd -> leak_i_tree -> estate -> Prop)
    (Pi_ri : estate -> instr_r -> leak_i_tree -> estate -> Prop)
    (Pi_i : estate -> instr -> leak_i_tree -> estate -> Prop)
    (Pfor_i : var_i -> seq Z -> estate -> cmd -> seq (seq leak_i_tree) -> estate -> Prop)
    (Pfun_i : Memory.mem -> funname -> seq value -> funname * leak_i_tree -> Memory.mem -> seq value -> Prop).

  Definition sem_Ind_nil_i : Prop :=
    forall s : estate, Pci s [::] LTempty s.

  Definition sem_Ind_cons_i : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd) (li : leak_i_tree) (lc : leak_i_tree),
      sem_I_i P s1 i li s2 -> Pi_i s1 i li s2 -> sem_c_i P s2 c lc s3 ->
      Pci s2 c lc s3 -> Pci s1 (i :: c) (LTSub [:: li; lc]) s3.

  Hypotheses
    (Hnil_i: sem_Ind_nil_i)
    (Hcons_i: sem_Ind_cons_i).

  Definition sem_Ind_mkI_i : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate) (li : leak_i_tree),
      sem_i_i P s1 i li s2 -> Pi_ri s1 i li s2 -> Pi_i s1 (MkI ii i) li s2.

  Hypothesis HmkI : sem_Ind_mkI_i.

  Definition sem_Ind_assgn_i : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v' (le lw : leak_e_tree),
      sem_pexpr_e gd s1 e = ok (v, le) ->
      truncate_val ty v = ok v' →
      write_lval_e gd x v' s1 = Ok error (s2, lw) ->
      Pi_ri s1 (Cassgn x tag ty e) (LTassgn (LSub [:: le ; lw])) s2.

  Definition sem_Ind_opn_i : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs) (lo : leak_e_tree),
      sem_sopn_e gd o s1 xs es = Ok error (s2, lo) ->
      Pi_ri s1 (Copn xs t o es) (LTopn lo) s2.

  Definition sem_Ind_if_true_i : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e_tree) (lc : leak_i_tree),
      sem_pexpr_e gd s1 e = ok (Vbool true, le) ->
      sem_c_i P s1 c1 lc s2 -> Pci s1 c1 lc s2 -> Pi_ri s1 (Cif e c1 c2) (LTcond le true lc) s2.

  Definition sem_Ind_if_false_i : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e_tree) (lc : leak_i_tree),
      sem_pexpr_e gd s1 e = ok (Vbool false, le) ->
      sem_c_i P s1 c2 lc s2 -> Pci s1 c2 lc s2 -> Pi_ri s1 (Cif e c1 c2) (LTcond le false lc) s2.

  Definition sem_Ind_while_true_i : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_i_tree) 
           (le : leak_e_tree) (lc' : leak_i_tree) (li : leak_i_tree),
      sem_c_i P s1 c lc s2 -> Pci s1 c lc s2 ->
      sem_pexpr_e gd s2 e = ok (Vbool true, le) ->
      sem_c_i P s2 c' lc' s3 -> Pci s2 c' lc' s3 ->
      sem_i_i P s3 (Cwhile a c e c') li s4 -> 
      Pi_ri s3 (Cwhile a c e c') li s4 -> 
      Pi_ri s1 (Cwhile a c e c') (LTwhile_true lc le lc' li) s4.

  Definition sem_Ind_while_false_i : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_i_tree) (le : leak_e_tree),
      sem_c_i P s1 c lc s2 -> Pci s1 c lc s2 ->
      sem_pexpr_e gd s2 e = ok (Vbool false, le) ->
      Pi_ri s1 (Cwhile a c e c') (LTwhile_false lc le) s2.

  Hypotheses
    (Hasgn_i: sem_Ind_assgn_i)
    (Hopn_i: sem_Ind_opn_i)
    (Hif_true_i: sem_Ind_if_true_i)
    (Hif_false_i: sem_Ind_if_false_i)
    (Hwhile_true_i: sem_Ind_while_true_i)
    (Hwhile_false_i: sem_Ind_while_false_i).

  Definition sem_Ind_for_i : Prop :=
    forall (s1 s2 : estate) (i : var_i) r wr (c : cmd) (lr : leak_e_tree) (lf: seq (seq leak_i_tree)),
      sem_range_e P s1 r = ok (wr, lr) ->
      sem_for_i P i wr s1 c lf s2 ->
      Pfor_i i wr s1 c lf s2 -> Pi_ri s1 (Cfor i r c) (LTfor lr lf) s2.

  Definition sem_Ind_for_nil_i : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor_i i [::] s c [::] s.

  Definition sem_Ind_for_cons_i : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd) (lc : leak_i_tree)
           (lf : seq (seq leak_i_tree)),
      write_var i w s1 = Ok error s1' ->
      sem_c_i P s1' c lc s2 -> Pci s1' c lc s2 ->
      sem_for_i P i ws s2 c lf s3 -> Pfor_i i ws s2 c lf s3 -> Pfor_i i (w :: ws) s1 c ([:: lc] :: lf) s3.

  Hypotheses
    (Hfor_i: sem_Ind_for_i)
    (Hfor_nil_i: sem_Ind_for_nil_i)
    (Hfor_cons_i: sem_Ind_for_cons_i).

  Definition sem_Ind_call_i : Prop :=
    forall (s1 : estate) (m2 : Memory.mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value) (l1 : leak_e_tree)
           (lf : funname * leak_i_tree) (lw : leak_e_tree),
      sem_pexprs_e gd s1 args = Ok error (vargs, l1) ->
      sem_call_i P (emem s1) fn vargs lf m2 vs -> Pfun_i (emem s1) fn vargs lf m2 vs ->
      write_lvals_e gd {| emem := m2; evm := evm s1 |} xs vs = Ok error (s2, lw) ->
      Pi_ri s1 (Ccall ii xs fn args) (LTcall l1 lf lw) s2.

  Definition sem_Ind_proc_i : Prop :=
    forall (m1 m2 : Memory.mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value) (lc : leak_i_tree),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem_c_i P s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      Pci s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun_i m1 fn vargs' (fn, lc) m2 vres'.

  Hypotheses
    (Hcall_i: sem_Ind_call_i)
    (Hproc_i: sem_Ind_proc_i).

  Fixpoint sem_Ind_i (e : estate) (l : cmd) (le : leak_i_tree) (e0 : estate) (s : sem_c_i P e l le e0) {struct s} :
    Pci e l le e0 :=
    match s in (sem_c_i _ e1 l0 l1 e2) return (Pci e1 l0 l1 e2) with
    | Eskip_i s0 => Hnil_i s0
    | @Eseq_i _ s1 s2 s3 i c li lc s0 s4 =>
        @Hcons_i s1 s2 s3 i c li lc s0 (@sem_I_Ind_i s1 i li s2 s0) s4 (@sem_Ind_i s2 c lc s3 s4) 
    end

  with sem_i_Ind_i (e : estate) (i : instr_r) (li : leak_i_tree) (e0 : estate) (s : sem_i_i P e i li e0) {struct s} :
    Pi_ri e i li e0 :=
    match s in (sem_i_i _ e1 i0 le1 e2) return (Pi_ri e1 i0 le1 e2) with
    | @Eassgn_i _ s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3 => @Hasgn_i s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3
    | @Eopn_i _ s1 s2 t o xs es lo e1 => @Hopn_i s1 s2 t o xs es lo e1
    | @Eif_true_i _ s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_true_i s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind_i s1 c1 lc s2 s0)
    | @Eif_false_i _ s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_false_i s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind_i s1 c2 lc s2 s0)
    | @Ewhile_true_i _ s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 h2 h3 h4 =>
      @Hwhile_true_i s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 (@sem_Ind_i s1 c lc s2 h1) h2 h3 (@sem_Ind_i s2 c' lc' s3 h3) 
          h4 (@sem_i_Ind_i s3 (Cwhile a c e1 c') lw s4 h4)
    | @Ewhile_false_i _ s1 s2 a c e1 c' lc le s0 e2 =>
      @Hwhile_false_i s1 s2 a c e1 c' lc le s0 (@sem_Ind_i s1 c lc s2 s0) e2
    | @Efor_i _ s1 s2 i0 r c wr lr lf s0 sf =>
      @Hfor_i s1 s2 i0 r wr c lr lf s0 sf
        (@sem_for_Ind_i i0 wr s1 c lf s2 sf)
    | @Ecall_i _ s1 m2 s2 ii xs f13 args vargs vs l1 lf l2 e2 s0 e3 =>
      @Hcall_i s1 m2 s2 ii xs f13 args vargs vs l1 lf l2 e2 s0
        (@sem_call_Ind_i (emem s1) f13 vargs m2 vs lf s0) e3
    end

  with sem_I_Ind_i (e : estate) (i : instr) (li : leak_i_tree) (e0 : estate) (s : sem_I_i P e i li e0) {struct s} :
    Pi_i e i li e0 :=
    match s in (sem_I_i _ e1 i0 le e2) return (Pi_i e1 i0 le e2) with
    | @EmkI_i _ ii i0 s1 s2 li s0 => @HmkI ii i0 s1 s2 li s0 (@sem_i_Ind_i s1 i0 li s2 s0)
    end

  with sem_for_Ind_i (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (lf : seq (seq leak_i_tree))
                     (e0 : estate) (s : sem_for_i P v l e l0 lf e0) {struct s} : Pfor_i v l e l0 lf e0 :=
    match s in (sem_for_i _ v0 l1 e1 l2 le e2) return (Pfor_i v0 l1 e1 l2 le e2) with
    | EForDone_i s0 i c => Hfor_nil_i s0 i c
    | @EForOne_i _ s1 s1' s2 s3 i w ws c lc lw e1 s0 s4 =>
      @Hfor_cons_i s1 s1' s2 s3 i w ws c lc lw e1 s0 (@sem_Ind_i s1' c lc s2 s0)
         s4 (@sem_for_Ind_i i ws s2 c lw s3 s4)
    end

  with sem_call_Ind_i (m : Memory.mem) (f13 : funname) (l : seq value) (m0 : Memory.mem)
                    (l0 : seq value) (lf : funname * leak_i_tree) (s : sem_call_i P m f13 l lf m0 l0) {struct s} :
                    Pfun_i m f13 l lf m0 l0 :=
    match s with
    | @EcallRun_i _ m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc_i m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem (sem_Ind_i Hsem) Hvres Hctout
    end.

End SEM_IND_I.

Lemma sem_sopn_cp gd o s1 xs es s2 l:
  sem_sopn_e gd o s1 xs es = ok (s2, l) ->
  sem_sopn gd o s1 xs es = ok (s2, lest_to_les l).
  Proof.
    rewrite /sem_sopn_e. t_xrbindP.
    move=> [yv yl] He h0 Hex [yv' yl'] Hw <- <-.
    rewrite /sem_sopn. t_xrbindP.
    move: const_prop_e_esP_sem_pexprs_e'. move=> H.
    move: (H gd s1 es (yv, yl) He). move=> -> /=.
    rewrite /= in Hex. rewrite Hex /=.
    move: (write_lvals_cp). move=> Hw'. move: (Hw' gd s1 xs h0 yv' yl' Hw).
    move=> -> /=. rewrite /lests_to_les /=. by rewrite cats0.
  Qed.

  Lemma sem_range_cp gd s r s2 l:
  sem_range_e gd s r = ok (s2, l) ->
  sem_range gd s r = ok (s2, lest_to_les l).
  Proof.
    rewrite /sem_range_e /=. elim: r. move=> [d e1] e2. t_xrbindP.
    move=> [yv yl] He h0 Hi [yv' yl'] He' h4 Hi' Hs Hl.
    rewrite /sem_range. move: const_prop_e_esP_sem_pexpr_e. move=> H.
    move: (H (p_globs gd) s e1 (yv, yl) He). move=> -> /=. rewrite Hi /=.
    move: const_prop_e_esP_sem_pexpr_e. move=> H'.
    move: (H' (p_globs gd) s e2 (yv', yl') He'). move=> -> /=. rewrite Hi' /=.
    rewrite -Hs -Hl /=. rewrite /lests_to_les /=. by rewrite cats0.
  Qed.
  
  
Section Sem_I_Leakages_proof.

Variable P:prog.
  
Notation gd := (p_globs P).

Variable l0 : leakage_i.

Let Pci s1 c lc s2 := sem_c_i P s1 c lc s2 ->
                      exists lc', sem P s1 c lc' s2 /\ lc' = lit_to_li l0 lc.

Let Pi_ri s1 i li s2 := sem_i_i P s1 i li s2 ->
                        exists li', sem_i P s1 i li' s2 /\ li' = (head l0 (lit_to_li l0 li)).

Let Pi_i s1 i li s2 := sem_I_i P s1 i li s2 ->
                       exists li', sem_I P s1 i li' s2 /\ li' =  (head l0 (lit_to_li l0 li)).

Let Pfor_i i zs s1 c lc s2 := sem_for_i P i zs s1 c lc s2 ->
                              exists lc', sem_for P i zs s1 c lc' s2
                                          /\ lc' = litss_to_liss (lit_to_li l0) lc.

Let Pfun_i m1 fd vargs lf m2 vres := sem_call_i P m1 fd vargs lf m2 vres ->
                                     exists lf', sem_call P m1 fd vargs lf' m2 vres /\ lf'.2 = lit_to_li l0 (lf.2).

Local Lemma Hnil_i : sem_Ind_nil_i Pci.
Proof.
  rewrite /sem_Ind_nil_i. move=> s. rewrite /Pci.
  move=> /= H. exists [::]. split. constructor.
  rewrite /lits_to_lis /=. auto.
Qed.

Local Lemma Hcons_i : sem_Ind_cons_i P Pci Pi_i.
Proof.
  rewrite /sem_Ind_cons_i.
  move=> s1 s2 s3 i c li lc Hi HPi Hc HPc.
  rewrite /Pi_i in HPi. rewrite /Pci in HPc.
  move: (HPi Hi). move=> [] x [] Hx Hlx. move: (HPc Hc).
  move=> [] x' [] Hx' [] Hlx'. rewrite /Pci.
  move=> H. exists (lit_to_li l0 (LTSub [:: li; lc])). split.
  rewrite /=. rewrite /lits_to_lis /=. rewrite -Hlx'. rewrite cats0.
  admit. auto.
  (*apply Eseq with s2. auto. auto.
  rewrite Hlx Hlx'. admit.*)
Admitted.

Local Lemma HmkI_i : sem_Ind_mkI_i P Pi_ri Pi_i.
Proof.
  rewrite /sem_Ind_mkI_i /=.
  move=> ii i s1 s2 li Hi Hpi.
  rewrite /Pi_ri in Hpi. move: (Hpi Hi).
  move=> [] li' [] Hii Hl. rewrite /Pi_i.
  move=> H /=. exists li'. split.
  apply EmkI. auto. auto.
Qed.

Local Lemma Hasgn_i : sem_Ind_assgn_i P Pi_ri.
Proof.
  rewrite /sem_Ind_assgn_i.
  move=> s1 s2 x tag ty e v v' le lw He Ht Hw.
  rewrite /Pi_ri /=. move=> H. exists (Lassgn (lests_to_les lest_to_les [:: le; lw])).
  rewrite /lests_to_les /=. rewrite cats0. split. apply Eassgn with v v'.
  move: const_prop_e_esP_sem_pexpr_e. move=> Hc.
  move: (Hc (p_globs P) s1 e (v, le) He). move=> /= He'. auto. auto.
  move: (write_lval_cp). move=> Hw'. move: (Hw' (p_globs P) s1 x v' s2 lw Hw).
  move=> ->. auto. auto.
Qed.

Local Lemma Hopn_i : sem_Ind_opn_i P Pi_ri.
Proof.
  rewrite /sem_Ind_opn_i. move=> s1 s2 t o xs es lo Ho.
  rewrite /Pi_ri. move=> He. exists (head l0 (lit_to_li l0 (LTopn lo))).
  split. apply Eopn. move: sem_sopn_cp. move=> Ho'.
  move: (Ho' gd o s1 xs es s2 lo Ho). by move=> -> /=. auto.
Qed.

Local Lemma Hif_true_i : sem_Ind_if_true_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_if_true_i. move=> s1 s2 e c1 c2 le lc He Hc Hp Hpi.
  rewrite /Pci in Hp. move: (Hp Hc). move=> [] lc' [] Hi Hl /=. rewrite -Hl /=.
  exists (Lcond (lest_to_les le) true lc').
  split. apply Eif_true. move: const_prop_e_esP_sem_pexpr_e.
  move=> He'. move: (He' gd s1 e (Vbool true, le) He). by move=> -> /=.
  auto. auto.
Qed.

Local Lemma Hif_false_i : sem_Ind_if_false_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_if_true_i. move=> s1 s2 e c1 c2 le lc He Hc Hp Hpi.
  rewrite /Pci in Hp. move: (Hp Hc). move=> [] lc' [] Hi Hl /=. rewrite -Hl /=.
  exists (Lcond (lest_to_les le) false lc').
  split. apply Eif_false. move: const_prop_e_esP_sem_pexpr_e.
  move=> He'. move: (He' gd s1 e (Vbool false, le) He). by move=> -> /=.
  auto. auto.
Qed.

Local Lemma Hwhile_true_i : sem_Ind_while_true_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_while_true_i.
  move=> s1 s2 s3 s4 a c e c' lc le lc' li Hc Hci He Hc' Hci' Hi Hii.
  rewrite /Pci in Hci'. rewrite /Pi_ri in Hii. rewrite /Pi_ri.
  move=> H. move: (Hci' Hc'). move=> [] lc'0 [] Hs Hsl /=.
  move: (Hii Hi). move=> [] li' [] Hsi Hsli /=. rewrite -Hsli -Hsl /=.
  exists (Lwhile_true (lit_to_li l0 lc) (lest_to_les le) lc'0 li').
  split. apply Ewhile_true with s2 s3. rewrite /Pci in Hci.
  move: (Hci Hc). move=> [] lc'1 [] Hp <- /=. auto.
  move: const_prop_e_esP_sem_pexpr_e. move=> Hhe.
  move: (Hhe gd s2 e (Vbool true, le) He). by move=> -> /=.
  auto. auto. auto.
Qed.

Local Lemma Hwhile_false_i : sem_Ind_while_false_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_while_false_i.
  move=> s1 s2 a c e c' lc le Hci Hpi He. rewrite /Pi_ri.
  move=> H. rewrite /Pci in Hpi. move: (Hpi Hci).
  move=> [] lc' [] Hs Hsl /=. rewrite -Hsl /=.
  exists (Lwhile_false lc' (lest_to_les le)). split.
  apply Ewhile_false. auto. move: const_prop_e_esP_sem_pexpr_e. move=> Hhe.
  move: (Hhe gd s2 e (Vbool false, le) He). by move=> -> /=. auto.
Qed.

Local Lemma Hfor_i : sem_Ind_for_i P Pi_ri Pfor_i.
Proof.
  rewrite /sem_Ind_for_i. move=> s1 s2 i r wr c lr lf.
  move=> /sem_range_cp Hr Hf. rewrite /Pfor_i /=.
  move=> H. move: (H Hf). move=> []  lc' [] Hf' Hl.
  rewrite /Pi_ri /=. move=> Hi. rewrite -Hl /=.
  exists (Lfor (lest_to_les lr) lc').  split. by apply Efor with wr. auto.
Qed.

Local Lemma Hfor_nil_i : sem_Ind_for_nil_i Pfor_i.
Proof.
  rewrite /sem_Ind_for_nil_i. move=> s i c.
  rewrite /Pfor_i. move=> Hf /=. exists [::].
  split. by apply EForDone. auto.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons_i P Pci Pfor_i.
Proof.
  rewrite /sem_Ind_for_cons_i. move=> s1 s1' s2 s3 i w ws c lc lf Hw Hc Hpi.
  move=> Hf Hpi'. rewrite /Pci in Hpi. rewrite /Pfor_i in Hpi'. rewrite /Pfor_i.
  move=> H. move: (Hpi Hc). move=> [] lc' [] Hs Hl. move: (Hpi' Hf).
  move=> [] lc'0 [] Hs' [] Hl' /=.
  exists (lits_to_lis (lit_to_li l0) [:: lc] :: litss_to_liss (lit_to_li l0) lf).
  split. rewrite -Hl' /=. rewrite /lits_to_lis /=. rewrite cats0. rewrite -Hl /=.
  apply EForOne with s1' s2. auto. auto. auto. auto.
Qed.
  
Local Lemma Hcall_i : sem_Ind_call_i P Pi_ri Pfun_i.
Proof.
  rewrite /sem_Ind_call_i. move=> s1 m2 s2 ii xs fn args vargs vs l1 lf lw.
  move=> Hes Hc Hpi Hws. rewrite /Pi_ri. rewrite /Pfun_i in Hpi. move=> H.
  move: (Hpi Hc). move=> [] lf' [] Hc' Hl /=. exists (head l0
        (let (f, li) := lf in
         [:: Lcall (lest_to_les l1)
               (f, lit_to_li l0 li)
               (lest_to_les lw)])). subst.
  split. subst. admit.
Admitted.

Local Lemma Hproc_i : sem_Ind_proc_i P Pci Pfun_i.
Proof.
  rewrite /sem_Ind_proc_i. move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hg Hm.
  move=> Hws Hci Hpi Hm' Hm''. rewrite /Pfun_i. move=> H.
  rewrite /Pci in Hpi. move: (Hpi Hci). move=> [] lc' [] Hpi' Hl.
  rewrite /=. rewrite -Hl /=. exists (fn, lc'). rewrite /=.
  split. apply EcallRun with f vargs s1 vm2 vres. auto.
  auto. auto. auto. auto. auto. auto.
Qed.


End Sem_I_Leakages_proof.

Section Sem_I_Sem_Leakages_proof.

Variable P:prog.
  
Notation gd := (p_globs P).

Variable l0 : leakage_i.

Let Pc s1 c lc s2 := sem P s1 c lc s2 ->
                       exists lc',  lc = (lit_to_li l0 lc') /\ sem_c_i P s1 c lc' s2.

Let Pi_r s1 i li s2 := sem_i P s1 i li s2 ->
                        exists li', li = (head l0 (lit_to_li l0 li')) /\  sem_i_i P s1 i li' s2.

Let Pi s1 i li s2 := sem_I P s1 i li s2 ->
                       exists li', li =  (head l0 (lit_to_li l0 li')) /\  sem_I_i P s1 i li' s2.

Let Pfor i zs s1 c lc s2 := sem_for P i zs s1 c lc s2 ->
                              exists lc',  lc = litss_to_liss (lit_to_li l0) lc' /\
                                           sem_for_i P i zs s1 c lc' s2.
                                          
Let Pfun m1 fd vargs lf m2 vres := sem_call P m1 fd vargs lf m2 vres ->
                                     exists lf', lf.2 = lit_to_li l0 (lf'.2) /\
                                                 sem_call_i P m1 fd vargs lf' m2 vres.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof.
  rewrite /sem_Ind_nil. move=> s. rewrite /Pc.
  move=> /= H. exists LTempty. split. auto. constructor.
Qed.


Local Lemma Hcons : sem_Ind_cons P Pc Pi.
Proof.
  rewrite /sem_Ind_cons.
  move=> s1 s2 s3 i c li lc Hi HPi Hc HPc.
  rewrite /Pi in HPi. rewrite /Pc in HPc.
  move: (HPi Hi). move=> [] x [] Hx Hlx. move: (HPc Hc).
  move=> [] x' [] Hx' [] Hlx'. rewrite /Pc.
  move=> H.
  admit. 
  (*apply Eseq with s2. auto. auto.
  rewrite Hlx Hlx'. admit.*)
Admitted.

Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
Proof.
  rewrite /sem_Ind_mkI. move=> ii i s1 s2 li Hs H.
  rewrite /Pi_r in H. move: (H Hs). move=> [] li' [] Hl Hi.
  rewrite /Pi. move=> H'. 



End Sem_I_Sem_Leakages_proof.





  


               
(* Here we need to write the theorem sem -> sem_e and sem_e -> sem *)

End Sem_I_Leakages_proof.


Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd * leak_i_tr :=
  match ir with
  | Cassgn x tag ty e =>
.    let (e, lt) := const_prop_e m e in
    let: (m,x, ltx) := const_prop_rv m x in
    let m := add_cpm m x tag ty e in
    (m, [:: MkI ii (Cassgn x tag ty e)], LT_iseq [:: LT_ile lt; LT_ile ltx])

  | Copn xs t o es =>
    (* TODO: Improve this *)
    let es := map (const_prop_e m) es in
    let: (m,xs, lts) := const_prop_rvs m xs in
)    (m, [:: MkI ii (Copn xs t o (unzip1 es)) ], 
         LT_iseq [ :: LT_ile (LT_seq (unzip2 es)) ; LT_ile lts])

  | Cif b c1 c2 =>
    let (b, ltb) := const_prop_e m b in
    match is_bool b with
    | Some b =>
      if b then let: (v1, cm1, ltc1) := const_prop const_prop_i m c1 in 
                     (v1, cm1, LT_ileli ltb ltc1) 
           else let: (v2, cm2, ltc2) := const_prop const_prop_i m c1 in 
                     (v2, cm2, LT_ileli ltb ltc2) 
    | None =>
      let: (m1,c1,lt1) := const_prop const_prop_i m c1 in
      let: (m2,c2,lt2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ], LT_ileli ltb (LT_iseq [:: lt1; lt2]))
    end

  | Cfor x (dir, e1, e2) c =>
    let (e1, lte1) := const_prop_e m e1 in
    let (e2, lte2) := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let: (_,c, ltc) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ], LT_ileli (LT_seq [:: lte1; lte2]) ltc)

  | Cwhile a c e c' =>
    let m := remove_cpm m (write_i ir) in
    let: (m',c, ltc) := const_prop const_prop_i m c in
    let (e, lte) := const_prop_e m' e in
    let: (_,c', ltc') := const_prop const_prop_i m' c' in
    let cw :=
      match is_bool e with
      | Some false => c
      | _          => [:: MkI ii (Cwhile a c e c')]
      end in
    (m', cw, LT_ikeep)
  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let: (m,xs,lt) := const_prop_rvs m xs in
    (m, [:: MkI ii (Ccall fi xs f (unzip1 es)) ], LT_ikeep)
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd * leak_i_tr :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,tin,p,c,tout,r) := f in
  let: (_, c, lt) := const_prop const_prop_i empty_cpm c in
  MkFun ii tin p c tout r.

Definition const_prop_prog (p:prog) : prog := map_prog const_prop_fun p.
