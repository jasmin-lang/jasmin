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


Inductive leaktrans_e :=
| LET_id
| LET_remove 
| LET_sub of seq leaktrans_e.

Inductive leak_e_tree :=
| LEempty
| LEIdx of Z
| LEAdr of pointer
| LESub of (seq leak_e_tree).

Inductive leakage_i_tree : Type :=
  | Lassgn_tree : leak_e_tree -> leakage_i_tree
  | Lopn_tree  : leak_e_tree ->leakage_i_tree
  | Lcond_tree  : leak_e_tree -> bool -> seq leakage_i_tree -> leakage_i_tree
  | Lwhile_true_tree : seq leakage_i_tree -> leak_e_tree -> seq leakage_i_tree -> leakage_i_tree -> leakage_i_tree
  | Lwhile_false_tree : seq leakage_i_tree -> leak_e_tree -> leakage_i_tree
  | Lfor_tree : leak_e_tree -> seq (seq leakage_i_tree) -> leakage_i_tree
  | Lcall_tree : leak_e_tree -> (funname * seq leakage_i_tree) -> leak_e_tree -> leakage_i_tree.

Notation leakage_c_tree := (seq leakage_i_tree).

Notation leakage_for_tree := (seq leakage_c_tree) (only parsing).

Notation leakage_fun_tree := (funname * leakage_c_tree)%type.

Fixpoint trans_leakage (lt: leaktrans_e) (le:leak_e_tree) : leak_e_tree :=
  match lt, le with 
  | LET_id, _ => le
  | LET_remove, _ => LEempty 
  | LET_sub lts, LESub les => LESub (map2 trans_leakage lts les)
  | LET_sub _  , le        => LEempty (* assert false *)
  end.

(* WRONG: Two diff leakages can end up getting same leak_e_tree in this case *)
(*Fixpoint les_to_lest (les : leakages_e) : leak_e_tree := 
  match les with 
  | [::] => LEempty 
  | l :: ls => match l with 
               | LeakAdr p => LESub [:: LEAdr p ; les_to_lest ls]
               | LeakIdx i => LESub [:: LEIdx i ; les_to_lest ls]
  end
  end.*)

Section LEST_TO_LES.

Variable (lest_to_les : leak_e_tree -> leakages_e).

Definition lests_to_les (l : seq leak_e_tree) : leakages_e := 
    flatten (map lest_to_les l).

End LEST_TO_LES.

Fixpoint lest_to_les (les : leak_e_tree) : leakages_e := 
  match les with 
  | LEempty => [::]
  | LEIdx i => [:: LeakIdx i]
  | LEAdr p => [:: LeakAdr p]
  | LESub les => lests_to_les lest_to_les les
  end.

Definition sword_of_int sz (e: pexpr*leaktrans_e) :=
  (Papp1 (Oword_of_int sz) e.1, LET_sub [::e.2]).

Definition sint_of_word sz (e: pexpr*leaktrans_e) :=
  if is_wconst sz e.1 is Some w
  then (Pconst (wunsigned w), LET_remove)
  else (Papp1 (Oint_of_word sz) e.1, LET_sub [::e.2]).

Definition ssign_extend sz sz' (e: pexpr*leaktrans_e) :=
  if is_wconst sz' e.1 is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (sign_extend sz w))), LET_remove)
  else (Papp1 (Osignext sz sz') e.1, LET_sub [:: e.2]).

Definition szero_extend sz sz' (e: pexpr*leaktrans_e) :=
  if is_wconst sz' e.1 is Some w
  then (Papp1 (Oword_of_int sz) (Pconst (wunsigned (zero_extend sz w))), LET_remove)
  else (Papp1 (Ozeroext sz sz') e.1, LET_sub [:: e.2]).

Definition snot_bool (e:pexpr*leaktrans_e) : (pexpr*leaktrans_e) :=
  match e.1 with
  | Pbool b      => (Pbool (negb b), LET_remove)
  | Papp1 Onot e0 => (e0, LET_sub [:: e.2])
  | _            => (Papp1 Onot e.1, LET_sub [:: e.2])
  end.

Definition snot_w (sz: wsize) (e:pexpr*leaktrans_e) : (pexpr*leaktrans_e) :=
  match is_wconst sz e.1 with
  | Some n => (wconst (wnot n),LET_remove)
  | None   => (Papp1 (Olnot sz) e.1, LET_sub [:: e.2])
  end.

Definition sneg_int (e: pexpr*leaktrans_e) : (pexpr*leaktrans_e) :=
  match e.1 with
  | Pconst z => (Pconst (- z), LET_remove)
  | Papp1 (Oneg Op_int) e' => (e', LET_sub [:: e.2])
  | _ => (Papp1 (Oneg Op_int) e.1, LET_sub [:: e.2])
  end.

Definition sneg_w (sz: wsize) (e:pexpr*leaktrans_e) : (pexpr*leaktrans_e) :=
  match is_wconst sz e.1 with
  | Some n => (wconst (- n)%R, LET_remove)
  | None   => (Papp1 (Oneg (Op_w sz)) e.1, LET_sub [:: e.2])
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
  match is_bool e1.1, is_bool e2.1 with
  | Some b, _ => if b then (e2.1, LET_sub [::LET_remove ; e2.2]) else (Pbool false, LET_sub [:: LET_remove; LET_remove])
  | _, Some b => if b then (e1.1, LET_sub [::e1.2; LET_remove]) else (Pbool false, LET_sub [:: LET_remove; LET_remove])
  | _, _      => (Papp2 Oand e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sor e1 e2 :=
   match is_bool e1.1, is_bool e2.1 with
  | Some b, _ => if b then (Pbool true, LET_sub [:: LET_remove; LET_remove]) else (e2.1, LET_sub [:: LET_remove; e2.2])
  | _, Some b => if b then (Pbool true, LET_sub [:: LET_remove; LET_remove]) else (e1.1, LET_sub [:: e1.2; LET_remove])
  | _, _       => (Papp2 Oor e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

(* ------------------------------------------------------------------------ *)

Definition sadd_int e1 e2 :=
  match is_const e1.1, is_const e2.1 with
  | Some n1, Some n2 => (Pconst (n1 + n2), LET_sub [:: LET_remove; LET_remove])
  | Some n, _ =>
    if (n == 0)%Z then (e2.1, LET_sub [:: LET_remove; e2.2]) 
                  else (Papp2 (Oadd Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, Some n =>
    if (n == 0)%Z then (e1.1, LET_sub [:: e1.2; LET_remove]) 
                  else (Papp2 (Oadd Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, _ => (Papp2 (Oadd Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sadd_w sz e1 e2 :=
  match is_wconst sz e1.1, is_wconst sz e2.1 with
  | Some n1, Some n2 => (wconst (n1 + n2), LET_sub [:: LET_remove; LET_remove])
  | Some n, _ => if n == 0%R then (e2.1, LET_sub [:: LET_remove; e2.2]) 
                             else (Papp2 (Oadd (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, Some n => if n == 0%R then (e1.1, LET_sub [:: e1.2; LET_remove]) 
                             else (Papp2 (Oadd (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, _ => (Papp2 (Oadd (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sadd ty :=
  match ty with
  | Op_int => sadd_int
  | Op_w sz => sadd_w sz
  end.

Definition ssub_int e1 e2 :=
  match is_const e1.1, is_const e2.1 with
  | Some n1, Some n2 => (Pconst (n1 - n2), LET_sub [:: LET_remove; LET_remove])
  | _, Some n =>
    if (n == 0)%Z then (e1.1, LET_sub [:: e1.2; LET_remove]) 
                  else (Papp2 (Osub Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, _ => (Papp2 (Osub Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition ssub_w sz e1 e2 :=
  match is_wconst sz e1.1, is_wconst sz e2.1 with
  | Some n1, Some n2 => (wconst (n1 - n2), LET_sub [:: LET_remove; LET_remove])
  | _, Some n => if n == 0%R then (e1.1, LET_sub [:: e1.2; LET_remove]) 
                             else (Papp2 (Osub (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, _ => (Papp2 (Osub (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition ssub ty :=
  match ty with
  | Op_int => ssub_int
  | Op_w sz => ssub_w sz
  end.

Definition smul_int e1 e2 :=
  match is_const e1.1, is_const e2.1 with
  | Some n1, Some n2 => (Pconst (n1 * n2), LET_sub [:: LET_remove; LET_remove])
  | Some n, _ =>
    if (n == 0)%Z then (Pconst 0, LET_sub [:: LET_remove; LET_remove])
    else if (n == 1)%Z then (e2.1, LET_sub [:: LET_remove; e2.2])
    else (Papp2 (Omul Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, Some n =>
    if (n == 0)%Z then (Pconst 0, LET_sub [:: LET_remove; LET_remove])
    else if (n == 1)%Z then (e1.1, LET_sub [:: e1.2; LET_remove])
    else (Papp2 (Omul Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  | _, _ => (Papp2 (Omul Op_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition smul_w sz e1 e2 :=
  match is_wconst sz e1.1, is_wconst sz e2.1 with
  | Some n1, Some n2 => (wconst (n1 * n2), LET_sub [:: LET_remove; LET_remove])
  | Some n, _ =>
    if n == 0%R then (@wconst sz 0, LET_sub [:: LET_remove; LET_remove])
    else if n == 1%R then (e2.1, LET_sub [::LET_remove ; e2.2])
    else (Papp2 (Omul (Op_w sz)) (wconst n) e2.1, LET_sub [::LET_remove ; e2.2])
  | _, Some n =>
    if n == 0%R then (@wconst sz 0, LET_sub [:: LET_remove; LET_remove])
    else if n == 1%R then (e1.1, LET_sub [::e1.2; LET_remove])
    else (Papp2 (Omul (Op_w sz)) e1.1 (wconst n), LET_sub [::e1.2; LET_remove])
  | _, _ => (Papp2 (Omul (Op_w sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition smul ty :=
  match ty with
  | Op_int => smul_int
  | Op_w sz => smul_w sz
  end.

Definition s_eq ty e1 e2 :=
  if eq_expr e1.1 e2.1 then (Pbool true, LET_sub [:: LET_remove; LET_remove])
  else
    match ty with
    | Op_int =>
      match is_const e1.1, is_const e2.1 with
      | Some i1, Some i2 => (Pbool (i1 == i2), LET_sub [:: LET_remove; LET_remove])
      | _, _             => (Papp2 (Oeq ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
      end
    | Op_w sz =>
      match is_wconst sz e1.1, is_wconst sz e2.1 with
      | Some i1, Some i2 => (Pbool (i1 == i2), LET_sub [:: LET_remove; LET_remove])
      | _, _             => (Papp2 (Oeq ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
      end
    end.

Definition sneq ty e1 e2 :=
  match is_bool (s_eq ty e1 e2).1 with
  | Some b => (Pbool (~~ b), LET_remove)
  | None      => (Papp2 (Oneq ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
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
  if eq_expr e1.1 e2.1 then (Pbool false, LET_remove)
  else match is_cmp_const ty e1.1, is_cmp_const ty e2.1 with
  | Some n1, Some n2 => (Pbool (n1 <? n2)%Z, LET_sub [:: LET_remove; LET_remove])
  | _      , _       => (Papp2 (Olt ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sle ty e1 e2 :=
  if eq_expr e1.1 e2.1 then (Pbool true, LET_remove)
  else match is_cmp_const ty e1.1, is_cmp_const ty e2.1 with
  | Some n1, Some n2 => (Pbool (n1 <=? n2)%Z, LET_sub [:: LET_remove; LET_remove])
  | _      , _       => (Papp2 (Ole ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sgt ty e1 e2 :=
  if eq_expr e1.1 e2.1 then (Pbool false, LET_remove)
  else match is_cmp_const ty e1.1, is_cmp_const ty e2.1 with
  | Some n1, Some n2 => (Pbool (n1 >? n2)%Z, LET_sub [:: LET_remove; LET_remove])
  | _      , _       => (Papp2 (Ogt ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sge ty e1 e2 :=
  if eq_expr e1.1 e2.1 then (Pbool true, LET_remove)
  else match is_cmp_const ty e1.1, is_cmp_const ty e2.1 with
  | Some n1, Some n2 => (Pbool (n1 >=? n2)%Z, LET_sub [:: LET_remove; LET_remove])
  | _      , _       => (Papp2 (Oge ty) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sbitw i (z: ∀ sz, word sz → word sz → word sz) sz e1 e2 :=
  match is_wconst sz e1.1, is_wconst sz e2.1 with
  | Some n1, Some n2 => (wconst (z sz n1 n2), LET_sub [:: LET_remove; LET_remove])
  | _, _ => (Papp2 (i sz) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition soint i f e1 e2 :=
  match is_const e1.1, is_const e2.1 with
  | Some n1, Some n2 =>  (Pconst (f n1 n2), LET_sub [:: LET_remove; LET_remove])
  | _, _ => (Papp2 (i Cmp_int) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sbituw i (z: signedness -> ∀ sz, word sz → word sz → word sz) u sz e1 e2 :=
  match is_wconst sz e1.1, is_wconst sz e2.1 with
  | Some n1, Some n2 =>
    if n2 == 0%R then (Papp2 (i (Cmp_w u sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
    else (wconst (z u sz n1 n2), LET_sub [:: LET_remove; LET_remove])
  | _, _ => (Papp2 (i (Cmp_w u sz)) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
  end.

Definition sdiv ty (e1 e2:pexpr*leaktrans_e) :=
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
  match is_wconst sz e1.1, is_wconst U8 e2.1 with
  | Some n1, Some n2 => (wconst (z sz n1 n2), LET_sub [:: LET_remove; LET_remove])
  | _, _ => (Papp2 (i sz) e1.1 e2.1, LET_sub ([:: e1.2; e2.2]))
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
  match (mapM force_int (map fst es) >>= sem_opN op) with
  | Ok (Vword sz w) => (Papp1 (Oword_of_int sz) (Pconst (wunsigned w)), LET_remove)
  | _ => (PappN op (unzip1 es), LET_sub ((unzip2 es)))
  end.

Definition s_if t e e1 e2 :=
  match is_bool e.1 with
  | Some b => if b then (e1.1, LET_sub [:: LET_remove; e1.2; LET_remove]) else (e2.1, LET_sub [::  LET_remove; LET_remove;e2.2])
  | None   => (Pif t e.1 e1.1 e2.1, 
               LET_sub ([:: e.2; e1.2; e2.2]))
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

Fixpoint map_lt_es (es: pexprs) (lt : leaktrans_e) : seq (pexpr * leaktrans_e) := 
  match es with 
  | [::] => [::]
  | e :: es' => (e, lt) :: map_lt_es es' lt
  end.

Fixpoint const_prop_e (m:cpm) e : (pexpr * leaktrans_e) :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _
    => (e, LET_remove)
  | Pvar  x       => if Mvar.get m x is Some n then (const n, LET_remove) else (e, LET_id)
  | Pglobal _     => (e, LET_id)
  | Pget  sz x e0  => let v := (const_prop_e m e0) in (Pget sz x v.1, LET_sub [:: v.2 ; LET_id])
  | Pload sz x e0  => let v := (const_prop_e m e0) in (Pload sz x v.1, LET_sub [:: v.2 ; LET_id])
  | Papp1 o e0     => let v := (const_prop_e m e0) in (s_op1 o v)
  | Papp2 o e1 e2 => let v1 := (const_prop_e m e1) in
                     let v2 := (const_prop_e m e2) in 
                     s_op2 o v1 v2 
  | PappN op es   => s_opN op (map (const_prop_e m) es) 
  | Pif t e0 e1 e2 => let v1 := (const_prop_e m e0) in
                      let v2 := (const_prop_e m e1) in 
                      let v3 := (const_prop_e m e2) in 
                      s_if t v1 v2 v3 
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

Definition const_prop_rv (m:cpm) (rv:lval) : cpm * lval * leaktrans_e :=
  match rv with
  | Lnone _ _    => (m, rv, LET_id)
  | Lvar  x      => (Mvar.remove m x, rv, LET_id)
  | Lmem  sz x e => let v := const_prop_e m e in (m, Lmem sz x v.1, LET_sub [::v.2; LET_id])
  | Laset sz x e => let v := const_prop_e m e in (Mvar.remove m x, Laset sz x v.1, LET_sub [::v.2; LET_id])
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals * leaktrans_e :=
  match rvs with
  | [::] => (m, [::], LET_sub [::])
  | rv::rvs =>
    let: (m,rv, lt)  := const_prop_rv m rv in
    let: (m,rvs, lts) := const_prop_rvs m rvs in
    (m, rv::rvs, LET_sub [:: lt ; lts])
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

Inductive leaktrans_i : Type:=
  | LETremove : leaktrans_i
  | LETkeep : leaktrans_i
  | LETleake : leaktrans_e -> leaktrans_i
  | LETsub0 : leaktrans_i -> leaktrans_i -> leaktrans_i
  | LETsub : leaktrans_i -> seq leaktrans_i -> leaktrans_i
  | LETsub1 : seq leaktrans_i -> leaktrans_i
  | LETsub2 : seq leaktrans_i -> seq leaktrans_i -> leaktrans_i
  | LETsub3 : leaktrans_i -> seq leaktrans_i -> seq leaktrans_i -> leaktrans_i.

Notation leaktrans_c := (seq leaktrans_i).

  Variable const_prop_i : cpm -> instr -> cpm * cmd * leaktrans_i.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd * leaktrans_c :=
    match c with
    | [::] => (m, [::], [::])
    | i::c =>
      let: (m,ic,lti) := const_prop_i m i in
      let: (m, c, ltc) := const_prop m c in
      (m, ic ++ c, ([:: lti] ++ ltc))
    end.

End CMD.

Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd * leaktrans_i :=
  match ir with
  | Cassgn x tag ty e =>
    let: (v, l1) := const_prop_e m e in
    let: (m,x, l2) := const_prop_rv m x in
    let m := add_cpm m x tag ty v in
    (m, [:: MkI ii (Cassgn x tag ty e)], (LETleake (LET_sub ([:: l1; l2]))))

  | Copn xs t o es =>
    (* TODO: Improve this *)
    let es := map (const_prop_e m) es in
    let: (m,xs, ls) := const_prop_rvs m xs in
    (m, [:: MkI ii (Copn xs t o (unzip1 es))], (LETleake (LET_sub [::LET_sub (unzip2 es); ls])))

  | Cif b c1 c2 =>
    let: (b, l) := const_prop_e m b in
    match is_bool b with
    | Some b =>
      let c := if b then c1 else c2 in
      let: (v1, cm1, lc1) := const_prop const_prop_i m c1 in
      let: (v2, cm2, lc2) := const_prop const_prop_i m c2 in 
      (if b then v1 else v2, if b then cm1 else cm2, LETsub3 LETremove lc1 lc2)
    | None =>
      let: (m1,c1, lc1) := const_prop const_prop_i m c1 in
      let: (m2,c2, lc2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ], (LETsub3 (LETleake l) lc1 lc2))
    end

  | Cfor x (dir, e1, e2) c =>
    let: (e1, l1) := const_prop_e m e1 in
    let: (e2, l2) := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let: (_,c, lc) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ], (LETsub (LETleake (LET_sub ([:: l1] ++ [:: l2]))) lc))

  | Cwhile a c e c' =>
    let m := remove_cpm m (write_i ir) in
    let: (m',c, lc) := const_prop const_prop_i m c in
    let: (e, l) := const_prop_e m' e in
    let: (_,c', lc') := const_prop const_prop_i m' c' in
    let: (cw, cwl) :=
      match is_bool e with
      | Some false => (c, (LETsub (LETleake LET_remove) lc))
      | _          => ([:: MkI ii (Cwhile a c e c')], (LETsub3 (LETleake l) lc lc'))
      end in
    (m', cw, cwl)
  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let: (m,xs, ls) := const_prop_rvs m xs in
    (m, [:: MkI ii (Ccall fi xs f (unzip1 es)) ], LETsub0 (LETleake (LET_sub (unzip2 es))) (LETleake ls))
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd * leaktrans_i :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,tin,p,c,tout,r) := f in
  let: (_, c, lc) := const_prop const_prop_i empty_cpm c in
  (MkFun ii tin p c tout r, lc).

Definition leaktrans_fs := seq (funname * (seq leaktrans_i)).

Print prog.

Check const_prop_fun.

Check fun_decls.

Print fun_decls.

Fixpoint get_funnames (fdls : seq fun_decl) : seq funname :=
match fdls with 
| [::] => [::]
| fd :: fds => fst fd :: get_funnames fds
end.

Fixpoint get_fundefs (fdls : seq fun_decl) : seq fundef :=
match fdls with 
| [::] => [::]
| fd :: fds => (snd fd) :: get_fundefs fds
end.

Fixpoint seq_fn_leaktrans_c (s1 : seq funname) (s2 : seq (fundef * seq leaktrans_i)) : seq (funname * (seq leaktrans_i)) :=
match s1, s2 with 
| x :: xl, y :: yl => (x, y.2) :: seq_fn_leaktrans_c xl yl 
| _, _ => [::]
end.

Fixpoint seq_fn_fd (s1 : seq funname) (s2 : seq (fundef * seq leaktrans_i)) : seq (funname * fundef) :=
match s1, s2 with 
| x :: xl, y :: yl => (x, y.1) :: seq_fn_fd xl yl 
| _, _ => [::]
end.

Definition get_fn_leaktrans_fs p := 
let fns := get_funnames (p_funcs p) in 
seq_fn_leaktrans_c fns (map const_prop_fun (get_fundefs (p_funcs p))).

Definition get_fds p := 
let fns := get_funnames (p_funcs p) in 
seq_fn_fd fns (map const_prop_fun (get_fundefs (p_funcs p))).

Definition const_prop_prog (p : prog) : (prog * leaktrans_fs) := 
({| p_globs := p_globs p; p_funcs := get_fds p |},
  (get_fn_leaktrans_fs p)).


(*Definition const_prop_prog (p:prog) := 
  map_prog const_prop_fun p. *)

(****** NEED TO REDO THIS ********)
(*Section LEAK_TRANS.

Variable (Ffs : seq (funname * seq leaktrans_i)).

Section LEAK_TRANS_LOOP.

  Variable (lrm_i : leaktrans_i -> leakage_i -> leakage_c).

  Definition lrm_c (lt: seq leaktrans_i) (lc:leakage_c) : leakage_c := 
    flatten (map2b lrm_i lt lc).

  Definition lrm_w_false (lt : leaktrans_e) (lt1 : seq leaktrans_i) (li: leakage_i) : leakage_i := 
    match li with
    | Lwhile_false lc1 le => 
      Lwhile_false (lrm_c lt1 lc1) (lest_to_les (trans_leakage lt (les_to_lest le)))
    | _ => (* absurd *)
      li
    end.

  Fixpoint lrm_w_true (lt : leaktrans_e) (lt1 lt2: seq leaktrans_i) (li: leakage_i) : leakage_i := 
    match li with
    | Lwhile_true lc1 le lc2 li => 
      Lwhile_true (lrm_c lt1 lc1) (lest_to_les (trans_leakage lt (les_to_lest le))) (lrm_c lt2 lc2) (lrm_w_true lt lt1 lt2 li)
    | _ => (* absurd *)
      li
    end.

Definition lrm_for (lt:seq leaktrans_i) (lfor:leakage_for) :=
    map (lrm_c lt) lfor.

  Definition lrm_fun (lf: leakage_fun) := 
    let fn := lf.1 in
    let lt := odflt [::] (get_fundef Ffs fn) in
    (fn, lrm_c lt lf.2).

End LEAK_TRANS_LOOP.

Fixpoint leaktrm_i (lt : leaktrans_i) (li : leakage_i) {struct li} : leakage_c :=
match lt, li with 
  | LETremove, _ => [::]
  | LETsub0 (LETleake lt1) (LETleake lt2), Lcall la lf le =>
    [:: Lcall (lest_to_les (trans_leakage lt1 (les_to_lest la))) 
              (lrm_fun leaktrm_i lf) 
              (lest_to_les (trans_leakage lt1 (les_to_lest le)))]
  | LETkeep, _ => [:: li]
    (* This is the case when b is evaluated to boolean then we make a choice *)
  | LETsub3 LETremove lt1 lt2, Lcond le b lc => [:: Lcond le b (lrm_c leaktrm_i (if b then lt1 else lt2) lc)]
  | LETsub3 (LETleake lt) lt1 lt2, Lcond le b lc =>
    (* This is the case when b is not evaluated to boolean *)
    [:: Lcond (lest_to_les (trans_leakage lt (les_to_lest le))) b (lrm_c leaktrm_i (if b then lt1 else lt2) lc)]
  | LETsub (LETleake lt1) lt2, Lfor le lfor => 
    [:: Lfor (lest_to_les (trans_leakage lt1 (les_to_lest le))) (lrm_for leaktrm_i lt2 lfor)]
  | LETsub (LETleake lt) lt1, (Lwhile_false _ _) =>
    [:: lrm_w_false leaktrm_i lt lt1 li]
  | LETsub3 (LETleake lt) lt1 lt2, (Lwhile_true _ _ _ _) =>
    [ :: lrm_w_true leaktrm_i lt lt1 lt2 li]
  | LETleake le, Lassgn le' => [:: Lassgn (lest_to_les (trans_leakage le (les_to_lest le')))]
  | LETleake le, Lopn le' => [:: Lopn (lest_to_les (trans_leakage le (les_to_lest le')))]
  | _, _ => [:: li]
end.

End LEAK_TRANS.*)

Section SEM_PEXPR_E.

Context (gd: glob_decls).

Fixpoint sem_pexpr_e (s:estate) (e : pexpr) : exec (value * leak_e_tree) :=
  match e with
  | Pconst z => ok (Vint z, LEempty)
  | Pbool b  => ok (Vbool b, LEempty)
  | Parr_init n => ok (Varr (WArray.empty n), LEempty)
  | Pvar x => Let v := get_var s.(evm) x in 
              ok (v, LEempty)
  | Pglobal g => Let v := get_global gd g in 
                 ok (v, LEempty)
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let vl := sem_pexpr_e s e in 
      Let i := to_int vl.1 in 
      Let w := WArray.get ws t i in
      ok ((Vword w), LESub [:: vl.2; (LEIdx i)])
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let vl2 := sem_pexpr_e s e in 
    Let w2 := to_pointer vl2.1 in
    let adr := (w1 + w2)%R in 
    Let w  := read_mem s.(emem) adr sz in
    ok (@to_val (sword sz) w, LESub [:: vl2.2; (LEAdr adr)])
  | Papp1 o e1 =>
    Let vl := sem_pexpr_e s e1 in
    Let v := sem_sop1 o vl.1 in 
    ok (v, LESub [:: vl.2])
  | Papp2 o e1 e2 =>
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v := sem_sop2 o vl1.1 vl2.1 in
    ok (v, LESub ([:: vl1.2] ++ [:: vl2.2]))
  | PappN op es =>
    Let vs := mapM (sem_pexpr_e s) es in
    Let v := sem_opN op (unzip1 vs) in
    ok (v, LESub (unzip2 vs))
  | Pif t e e1 e2 =>
    Let vl := sem_pexpr_e s e in
    Let b := to_bool vl.1in
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v1 := truncate_val t vl1.1 in
    Let v2 := truncate_val t vl2.1 in
    ok (if b then v1 else v2, LESub ([:: vl.2] ++ [:: vl1.2] ++ [:: vl2.2]))
  end.

Definition sem_pexprs_e s es :=
  Let vls := mapM (sem_pexpr_e s) es in
  ok (unzip1 vls, LESub (unzip2 vls)).

Definition write_lval_e (l:lval) (v:value) (s:estate) : exec (estate * leak_e_tree) :=
  match l with
  | Lnone _ ty => Let x := write_none s ty v in ok (x, LEempty)
  | Lvar x => Let v' := write_var x v s in ok(v', LEempty)
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let vl := sem_pexpr_e s e in 
    Let ve := to_pointer vl.1 in
    let p := (vx + ve)%R in
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok ({| emem := m;  evm := s.(evm) |}, LESub [:: vl.2; (LEAdr p)])
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let vl := sem_pexpr_e s i in 
    Let i := to_int vl.1 in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |}, LESub [:: vl.2; (LEIdx i)])
  end.

Definition write_lvals_e (s:estate) xs vs :=
   fold2 ErrType (fun l v sl => Let sl' := write_lval_e l v sl.1 in ok (sl'.1, LESub [:: sl.2 ; sl'.2]))
      xs vs (s, LEempty).


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

  Let P e : Prop := sem_pexpr gd s e = flatten_exec (sem_pexpr_e gd s e).

  Let Q (es:pexprs) : Prop := mapM (sem_pexpr gd s) es = flatten_execs (mapM (sem_pexpr_e gd s) es).


  Lemma const_prop_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    (*apply: pexprs_ind_pair; subst P Q; split => /=.*) admit.
  Admitted.

Lemma write_lval_cp s1 x v:
  write_lval gd x v s1 = flatten_estate (write_lval_e gd x v s1).
Proof.
admit.
Admitted.

Lemma write_lvals_cp s1 x v:
  write_lvals gd x v s1 = flatten_estate (write_lvals_e gd x v s1).
Proof.
admit.
Admitted.

End Sem_e_Leakages_proof.

Section SEM_E.

Variable P:prog.
Notation gd := (p_globs P).

Definition sem_range_e (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let vl1 := sem_pexpr_e gd s pe1 in 
  Let i1 := to_int vl1.1 in 
  Let vl2 := sem_pexpr_e gd s pe2 in 
  Let i2 := to_int vl2.1 in
  ok (wrange d i1 i2, LESub ([:: vl1.2] ++ [:: vl2.2])).

Definition sem_sopn_e gd o m lvs args := 
  Let vas := sem_pexprs_e gd m args in
  Let vs := exec_sopn o vas.1 in 
  Let ml := write_lvals_e gd m lvs vs in
  ok (ml.1, LESub ([:: vas.2] ++ [::ml.2])).


Inductive sem_e : estate -> cmd -> leakage_c_tree -> estate -> Prop :=
| Eskip_e s :
    sem_e s [::] [::] s

| Eseq_e s1 s2 s3 i c li lc :
    sem_I_e s1 i li s2 -> sem_e s2 c lc s3 -> sem_e s1 (i::c) (li :: lc) s3

with sem_I_e : estate -> instr -> leakage_i_tree -> estate -> Prop :=
| EmkI_e ii i s1 s2 li:
    sem_i_e s1 i li s2 ->
    sem_I_e s1 (MkI ii i) li s2

with sem_i_e : estate -> instr_r -> leakage_i_tree -> estate -> Prop :=
| Eassgn_e s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr_e gd s1 e = ok (v,l1) ->
    truncate_val ty v = ok v' →
    write_lval_e gd x v' s1 = ok (s2, l2) ->
    sem_i_e s1 (Cassgn x tag ty e) (Lassgn_tree (LESub [::l1 ;l2])) s2

| Eopn_e s1 s2 t o xs es lo:
    sem_sopn_e gd o s1 xs es = ok (s2, lo) ->
    sem_i_e s1 (Copn xs t o es) (Lopn_tree lo) s2

| Eif_true_e s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool true, le) ->
    sem_e s1 c1 lc s2 ->
    sem_i_e s1 (Cif e c1 c2) (Lcond_tree le true lc) s2

| Eif_false_e s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool false, le) ->
    sem_e s1 c2 lc s2 ->
    sem_i_e s1 (Cif e c1 c2) (Lcond_tree le false lc) s2

| Ewhile_true_e s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem_e s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool true, le) ->
    sem_e s2 c' lc' s3 ->
    sem_i_e s3 (Cwhile a c e c') lw s4 ->
    sem_i_e s1 (Cwhile a c e c') (Lwhile_true_tree lc le lc' lw) s4

| Ewhile_false_e s1 s2 a c e c' lc le:
    sem_e s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool false, le) ->
    sem_i_e s1 (Cwhile a c e c') (Lwhile_false_tree lc le) s2

| Efor_e s1 s2 (i:var_i) r c wr lr lf:
    sem_range_e s1 r = ok (wr, lr) ->
    sem_for_e i wr s1 c lf s2 ->
    sem_i_e s1 (Cfor i r c) (Lfor_tree lr lf) s2

| Ecall_e s1 m2 s2 ii xs f args vargs vs l1 lf l2:
    sem_pexprs_e gd s1 args = ok (vargs, l1) ->
    sem_call_e s1.(emem) f vargs lf m2 vs ->
    write_lvals_e gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i_e s1 (Ccall ii xs f args) (Lcall_tree l1 lf l2) s2

with sem_for_e : var_i -> seq Z -> estate -> cmd -> leakage_for_tree -> estate -> Prop :=
| EForDone_e s i c :
    sem_for_e i [::] s c [::] s

| EForOne_e s1 s1' s2 s3 i w ws c lc lw :
    write_var i (Vint w) s1 = ok s1' ->
    sem_e s1' c lc s2 ->
    sem_for_e i ws s2 c lw s3 ->
    sem_for_e i (w :: ws) s1 c (lc :: lw) s3

with sem_call_e : Memory.mem -> funname -> seq value -> leakage_fun_tree -> Memory.mem -> seq value -> Prop :=
| EcallRun_e m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem_e s1 f.(f_body) lc (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call_e m1 fn vargs' (fn, lc) m2 vres'.

End SEM_E.

Section SEM_LEAKAGES_PROOF.


Lemma sem_range_cp p s1 r:
  sem_range p s1 r = flatten_range (sem_range_e p s1 r).
Proof.
admit.
Admitted.

(** NEED TO HAVE A THEOREM ABOUT SEM AND SEM_E **)


(*if b[1] then a[1] else a[2]   [ LeakId 1; LeakId 1; LeakId 2]
                           LEsub [ LEId 1; LEId 1; LEId 2]

(b[1] + a[1]) + a[2]         [ LeakId 1; LeakId 1; LeakId 2]
                        LEsub [LEsub [ LEId 1; LEId 1]; LEid 2]*)




