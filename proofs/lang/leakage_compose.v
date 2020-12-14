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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Section ALL.

  Context (A:Type) (P: A -> Type) (f :  ∀ a, P a).

  Fixpoint mk_allT (l:seq A) : allT P l := 
    match l with 
    | [::] => tt
    | a::l => (f a, mk_allT l)
    end.

  Fixpoint on_nth d (h:P d) (l:seq A) : ∀ i, P (nth d l i) := 
   match l return ∀ i, P (nth d l i) with
   | [::] => fun i => 
     match i with 
     | 0 => h
     | _.+1 => h
     end
   | a::l => fun i =>
     match i with
     | 0 => f a
     | i.+1 => on_nth h l i
     end
   end.

  Lemma on_nthP d (h:P d) l i : i < size l -> on_nth h l i = f (nth d l i).
  Proof. by elim: l i => [ | a l hrec] [ | i] //= /hrec. Qed.

End ALL.

Local Unset Elimination Schemes.

Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)

Inductive leak_i : Type :=
  | Lassgn : leak_e -> leak_i
  | Lcond  : leak_e -> bool -> leak_c -> leak_i
  | Lwhile_true : leak_c -> leak_e -> leak_c -> leak_i -> leak_i 
  | Lwhile_false : leak_c -> leak_e -> leak_i
  | Lfor : leak_e -> leak_for -> leak_i
  | Lcall : leak_e -> (funname * leak_c) -> leak_e -> leak_i
with leak_c : Type :=
  | L0 : leak_c
  | LC : leak_i -> leak_c -> leak_c
with leak_for : Type :=
  | LF0 : leak_for
  | LFC : leak_c -> leak_for -> leak_for.

Notation Lopn := Lassgn (only parsing).

Notation leak_fun := (funname * leak_c)%type.

Delimit Scope LC_scope with LC.
Bind Scope LC_scope with leak_c.

Infix "::" := LC : LC_scope.
Notation "[ :: ]" := L0 : LC_scope.

Delimit Scope LF_scope with LF.
Bind Scope LF_scope with leak_for.

Infix "::" := LFC : LF_scope.
Notation "[ :: ]" := LF0 : LF_scope.

Fixpoint cat_lc (s1 s2:leak_c) : leak_c := 
  match s1 with
  | [::]%LC => s2
  | (x :: s1')%LC => x :: cat_lc s1' s2
  end.

Infix "++" := cat_lc : LC_scope.

Fixpoint flatten_lf (s : leak_for) : leak_c := 
  match s with
  | [::]%LF      => [::]
  | (lc :: s)%LF => lc ++ (flatten_lf s)
  end.

(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)
Section LEAK_E_RECT.
  Context (P:leak_e -> Type)
    (HE : P LEmpty)
    (HI : ∀ z, P (LIdx z))
    (HA : ∀ p, P (LAdr p))
    (HS : ∀ les, (∀ i, i < size les -> P (nth LEmpty les i)) -> P (LSub les)).

  Fixpoint leak_e_rect (le:leak_e) : P le := 
    match le with
    | LEmpty => HE
    | LIdx z => HI z
    | LAdr p => HA p 
    | LSub les => HS (fun i hi => on_nth leak_e_rect HE les i)
    end.

End LEAK_E_RECT.

Arguments leak_e_rect: clear implicits.
(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)

(* Leakage transformer for expressions *)
Inductive leak_e_tr :=
| LT_id (* preserve *)
| LT_remove (* remove *)
| LT_subi_c : nat -> leak_e_tr -> leak_e_tr (* projection *) (* FIXME: change Z into nat *) (** Fixed **)
| LT_seq : seq leak_e_tr -> leak_e_tr. (* parallel transformations *)

Definition LT_subi n := LT_subi_c n LT_id.

Parameter name : eqType.

Inductive pattern := 
  | Pany of option name 
  | Pempty 
  | Pidx of name 
  | Padr of name
  | Psub of seq pattern.

Inductive leak_expr :=
  | LS_ptr of pointer 
  | LS_z   of Z
  | LS_var of name 
  | LS_add of leak_expr & leak_expr 
  | LS_mul of leak_expr & leak_expr. 

Inductive leak_tr := 
  | Match of leak_tr & pattern & leak_tr
  | Empty 
  | Var of name 
  | Idx of leak_expr 
  | Adr of leak_expr
  | Sub of seq leak_tr.

Inductive val := 
  | Vptr of pointer
  | Vz   of Z
  | Vl   of leak_e.


Definition env := seq (name * val).

Definition get_l (env:env) x := 
  match assoc env x with 
  | Some (Vl e) => e 
  | _           => LEmpty 
  end.
  
Fixpoint eval_expr env e : val := 
  match  e with 
  | LS_ptr p => Vptr p 
  | LS_z   z => Vz z 
  | LS_var x => odflt (Vz 0) (assoc env x) 
  | LS_add _ _ => Vz 0 
  | LS_mul _ _ => Vz 0 
  end. 

Definition eval_expr_z env e :=
  match eval_expr env e with
  | Vz z => z
  | _    => 0%Z
  end.

Definition eval_expr_a env e :=
  match eval_expr env e with
  | Vptr p => p
  | _      => 0%R
  end.

Section F2.
 Context (A B C : Type) (f: C -> A -> B -> C).
 Fixpoint fold2 c la lb := 
   match la, lb with
   | [::], _ | _, [::] => c
   | a::la, b::lb => fold2 (f c a b) la lb
   end.
End F2.
  
Fixpoint eval_pattern env pat le := 
  match pat, le with
  | Pany None    , _ => env
  | Pany (Some n), _ => (n,Vl le)::env
  | Pempty, LEmpty   => env
  | Pidx n, LIdx z   => (n, Vz z)::env
  | Padr n, LAdr p   => (n, Vptr p)::env
  | Psub pats, LSub les => fold2 eval_pattern env pats les
  | _, _ => [::]
  end.

Fixpoint eval (env:env) (lt: leak_tr) : leak_e := 
  match lt with
  | Empty => LEmpty
  | Var x => get_l env x 
  | Idx e => LIdx (eval_expr_z env e)
  | Adr e => LAdr (eval_expr_a env e)
  | Sub lts => LSub (map (eval env) lts)
  | Match lt pat clt =>
    let le := eval env lt in
    let env := eval_pattern env pat le in
    eval env clt 
  end.

Parameter nstk : name.
Parameter ntopleak : name.

Definition leak_E (lt:leak_tr) (stk:pointer) (l:leak_e) := 
  eval [::(nstk, Vptr stk); (ntopleak, Vl l)] lt.

Definition LT_map_named (ntopname:name) (l:seq (name * leak_tr)) := 
  Match (Var ntopname) 
        (Psub (map (fun p => Pany (Some p.1)) l))
        (Sub  (map snd l)).

Definition LT_map (lts : seq leak_tr) := 
  LT_map_named ntopleak (map (fun lt => (ntopleak, lt)) lts).




Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)







  

x = Lsub [Lsub [Lidx z, Lempty]; Lsub[Ladr p, Lempty]]

match x with
| Lsub [a; b] ->
  match a with
  | Lsub [a1; a2] ->
    match a1 with
    | Lidx z ->
      mathc


match x with
| Idx z -> z

Inductive leak_e_tr := 
 | Destr_empty  
 | Destr_idx   of name * leak_e_tr
 | Destr_adr   of name * leak_e_tr
 | Destr_sub   of name * leak_e_tr
 | Destr_subi  of nat * name * leak_e_tr
 | Constr_empty 
 | Constr_id   of name
 | Constr_idx  of name 
 | Constr_adr  of name 
 | Constr_sub  of leak_e_tr list  

LT_map 
Destr_sub "l1" (Constr_sub [





Section LEAK_E_RECT.

  Context
    (P: leak_e_tr → Type)
    (Hid: P LT_id) 
    (Hrm: P LT_remove)
    (Hsubi: forall i lt, P lt -> P (LT_subi_c i lt))
    (Hseq : forall lts, (∀ i, i < size lts -> P (nth LT_id lts i)) -> P (LT_seq lts)).

  Fixpoint leak_e_tr_rect (lt:leak_e_tr) : P lt := 
    match lt with
    | LT_id          => Hid
    | LT_remove      => Hrm
    | LT_subi_c i lt => Hsubi i (leak_e_tr_rect lt)
    | LT_seq lts     => Hseq (fun i hi => on_nth leak_e_tr_rect Hid lts i)
    end.

End LEAK_E_RECT.
Arguments leak_e_tr_rect: clear implicits.
Definition leak_e_tr_ind := leak_e_tr_rect.

Fixpoint leak_E (lt : leak_e_tr) (l : leak_e) : leak_e := 
  match lt, l with
  | LT_seq lts, LSub xs => LSub (map2 leak_E lts xs)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi_c i lt1, LSub xs => leak_E lt1 (nth LEmpty xs i)
  | _, _ => LEmpty
  end.

Fixpoint wf_E (lt : leak_e_tr) (l : leak_e) : bool := 
  match lt, l with
  | LT_seq lts, LSub xs => all2 wf_E lts xs
  | LT_id, _ => true 
  | LT_remove, _ => true 
  | LT_subi_c i lt1, LSub xs => (i < size xs) && wf_E lt1 (nth LEmpty xs i)
  | _, _ => false 
  end.

Fixpoint compose_e (lt1 lt2: leak_e_tr) {struct lt1} := 
 match lt1, lt2 with
 | LT_id, _ => lt2
 | _, LT_id => lt1
 | LT_remove, _ => LT_remove
 | _, LT_remove => LT_remove
 | LT_subi_c n lt1, lt2 => LT_subi_c n (compose_e lt1 lt2)
 | LT_seq lts1, LT_subi_c n lt2 => 
   LT_subi_c n (on_nth (fun lt1 => compose_e lt1 lt2) (d:= LT_id) LT_id lts1 n)
 | LT_seq lt1, LT_seq lt2 => LT_seq (map2 compose_e lt1 lt2)
 end.

Lemma compose_e_idlt lt : compose_e LT_id lt = lt.
Proof. done. Qed.
Lemma compose_e_ltid lt : compose_e lt LT_id = lt.
Proof. by case: lt. Qed.

Lemma compose_e_rmlt lt : compose_e LT_remove lt = LT_remove.
Proof. by case: lt. Qed.

Lemma compose_e_ltrm lt : compose_e lt LT_remove = LT_remove.
Proof. by case: lt. Qed.

Lemma leak_E_empty lt : leak_E lt LEmpty = LEmpty.
Proof. by elim: lt. Qed.

Lemma all2_size (A B:Type) (P:A->B->bool) l1 l2 : all2 P l1 l2 -> size l1 = size l2.
Proof.
  elim: l1 l2 => [ | a l1 hrec] [ | b l2] //=.
  by move=> /andP [_ /hrec ->].
Qed.

Lemma size_map2 (A B C:Type) (f:A->B->C) l1 l2 : size (map2 f l1 l2) = minn (size l1) (size l2).
Proof. by rewrite map2E size_map size_zip. Qed.

Lemma all2_nth (A B:Type) d1 d2 (P:A->B->bool) l1 l2 n : n < size l1 -> all2 P l1 l2 -> P (nth d1 l1 n) (nth d2 l2 n).
Proof.
  elim: l1 l2 n => [ | a l1 hrec] [ | b l2] [ | i] //=. 
  + by move=> _ /andP [].
  by move=> /hrec h /andP [_ /h].
Qed.

Lemma nth_map2 (A B C:Type) (f:A->B->C) d d1 d2 l1 l2 i : 
  size l1 = size l2 -> i < size l1 -> 
  nth d (map2 f l1 l2) i = f (nth d1 l1 i) (nth d2 l2 i).
Proof.
  by move=> hsz hi; rewrite map2E (nth_map (d1,d2)) ?nth_zip // size_zip -hsz minnn. 
Qed.

Lemma all2R  (A B:Type) d1 d2 (P:A->B->bool) l1 l2 : 
  reflect (size l1 = size l2 /\ forall i, i < size l1 -> P (nth d1 l1 i) (nth d2 l2 i)) 
          (all2 P l1 l2).
Proof.
  elim: l1 l2 => [ | a l1 hrec] [ | b l2] /=. 
  + by constructor.
  + by constructor => -[].
  + by constructor => -[].
  apply (equivP andP); split.
  + by move=> [h1 /hrec [-> h2]]; split => //; case.
  move=> [] [] h1 h2; split; first by apply (h2 0).
  by apply /hrec; split => // i hi; apply (h2 (i.+1) hi).
Qed.

Lemma compose_eP lt1 lt2 le : 
   wf_E lt1 le -> wf_E lt2 (leak_E lt1 le) -> 
   leak_E (compose_e lt1 lt2) le = leak_E lt2 (leak_E lt1 le) /\
   wf_E (compose_e lt1 lt2) le.
Proof.
elim: lt1 lt2 le.
+ by move=> lt2 le; rewrite compose_e_idlt.
+ by move=> lt2 le; rewrite compose_e_rmlt leak_E_empty.
+ move=> n lt1 hrec lt2 le.
  case: lt2.
  + by rewrite compose_e_ltid.
  + by rewrite compose_e_ltrm.
  + move=> n' lt2 /=; case: le => //= les.
    by move=> /andP [-> hw1]; apply (hrec (LT_subi_c n' lt2) _ hw1).
  move=> lt2 /=; case: le => //= les.
  by move=> /andP [-> hw1]; apply (hrec (LT_seq lt2) _ hw1).
move=> lts1 hrec lt2 le.
case: lt2.
+ by rewrite compose_e_ltid.
+ by rewrite compose_e_ltrm.
+ move=> n lt2 /=; case: le => //=.
  move=> les hall2 /andP.
  have eqsz := all2_size hall2.
  rewrite size_map2 -eqsz minnn => -[hsz1]; rewrite hsz1.
  rewrite (nth_map2 _ _ LT_id LEmpty eqsz hsz1) on_nthP //.
  by apply hrec => //; apply all2_nth.
move=> lts2; case: le => //= les /(all2R LT_id LEmpty) [eq1 hall2_w].
move=> /(all2R LT_id LEmpty) []; rewrite size_map2 -eq1 minnn => eq2.
rewrite eq2 => hall2_e.
have hir:  ∀ i, i < size lts1 -> 
    let lt2 := nth LT_id lts2 i in
    let le := nth LEmpty les i in
    leak_E (compose_e (nth LT_id lts1 i) lt2) le = leak_E lt2 (leak_E (nth LT_id lts1 i) le)
    ∧ wf_E (compose_e (nth LT_id lts1 i) lt2) le.
+ move=> i hi; apply hrec => //.
  + by apply hall2_w.
  by have := hall2_e _ hi;rewrite (nth_map2 _ LEmpty LT_id LEmpty).
have := size_map2 leak_E lts1 les; rewrite -eq1 minnn -eq2 => eq3.
have eq4 : size (map2 compose_e lts1 lts2) = size les.
+ by rewrite size_map2 -eq1 eq2 minnn.
split.
+ f_equal; apply: (@eq_from_nth _ LEmpty); rewrite !size_map2 eq2 -eq1 !minnn //.
  move=> i hi; rewrite !(nth_map2 _ LEmpty LT_id LEmpty); try congruence.
  rewrite (nth_map2 _ LT_id LT_id LT_id); try congruence.
  by apply hir.
apply /(all2R LT_id LEmpty); split => //.
rewrite size_map2 eq2 minnn => i hi.
rewrite /size_map2; rewrite (nth_map2 _ LT_id LT_id LT_id); try congruence.
by apply hir.
Qed.

(* Leakge transformer for instructions *)
Inductive leak_i_tr :=
(* | LT_ikeep : leak_i_tr *)
(* Keep the structure *)
| LT_ile : leak_e_tr -> leak_i_tr  (* assign and op *)
| LT_icond : leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr (* if *)
| LT_iwhile : seq leak_i_tr -> leak_e_tr -> seq leak_i_tr -> leak_i_tr (* while *)
| LT_ifor : leak_e_tr -> seq (seq leak_i_tr) -> leak_i_tr
| LT_icall : leak_e_tr -> leak_e_tr -> leak_i_tr
(* Modify the structure *)
| LT_iremove : leak_i_tr
| LT_iadd     : leak_e -> leak_i_tr
| LT_icond_eval : bool -> seq leak_i_tr -> leak_i_tr
| LT_ifor_unroll: seq (seq leak_i_tr) -> leak_i_tr.

Notation leak_c_tr := (seq leak_i_tr).

Definition leak_f_tr := seq (funname * leak_c_tr).

Definition dummy_li := Lassgn LEmpty.



Section Add.
  Context (leak_C : leak_c_tr -> leak_c -> leak_c) (lc:leak_c).
  Fixpoint leak_add lt : leak_c := 
    match lt with
    | LT_iadd le :: lt => Lassgn le :: leak_add lt
    | _ => leak_C lt lc
    end.

  Context (wf_C : leak_c_tr -> leak_c -> bool) (lc':leak_c).
  Fixpoint wf_add lt : bool := 
    match lt with
    | LT_iadd li :: lt => wf_add lt
    | _ => wf_C lt lc'
    end.

End Add.

Section Body.
  Context (leak_I : leak_i_tr -> leak_i -> leak_i) 
          (leak_C : leak_c_tr -> leak_c -> leak_c)
          (leak_F : seq leak_c_tr -> leak_for -> leak_for).

  Definition leak_body lt lc : leak_c := 
    match lt, lc with
    | LT_iremove :: lt, (_ :: lc)%LC => leak_C lt lc
    | LT_icond_eval _ lt1 :: lt2, (Lcond _ _ lc1 :: lc2)%LC => 
      leak_C lt1 lc1 ++ leak_C lt2 lc2
    | LT_icond_eval _ lt1 :: lt2, (Lwhile_false lc1 _ :: lc2)%LC => leak_C lt1 lc1 ++ leak_C lt2 lc2 
    | LT_ifor_unroll lts :: lt, (Lfor le lcs :: lc)%LC => 
      flatten_lf (leak_F lts lcs) ++ leak_C lt lc 
    | lti :: lt, (li :: lc)%LC => leak_I lti li :: leak_C lt lc 
    | [::], [::]%LC => [::]
    | _, _ => [::] (* Error *)
    end.

  Context (wf_I : leak_i_tr -> leak_i -> bool) 
          (wf_C : leak_c_tr -> leak_c -> bool)
          (wf_F : seq leak_c_tr -> leak_for -> bool).

  Definition wf_body lt lc : bool := 
    match lt, lc with
    | LT_iremove :: lt, (_ :: lc)%LC => wf_C lt lc
    | LT_icond_eval b lt1 :: lt2, (Lcond _ b' lc1 :: lc2)%LC => (b == b') && wf_C lt1 lc1 && wf_C lt2 lc2
    | LT_icond_eval b lt1 :: lt2, (Lwhile_false lc1 _ :: lc2)%LC => ~~b && wf_C lt1 lc1 && wf_C lt2 lc2 
    | LT_ifor_unroll lts :: lt, (Lfor le lcs :: lc)%LC => wf_F lts lcs && wf_C lt lc 
    | lti :: lt, (li :: lc)%LC => wf_I lti li && wf_C lt lc 
    | [::], [::]%LC => true
    | _, _ => false 
    end.

End Body.

Section Leak_I.

Variable leak_Fun : funname -> leak_c_tr.

Fixpoint leak_C (lt:leak_c_tr) (lc: leak_c) {struct lc} : leak_c :=
  leak_add (leak_body leak_I leak_C leak_F) lc lt

with leak_I (lt:leak_i_tr) (li : leak_i) {struct li} : leak_i :=
  match lt, li with
  | LT_ile lte, Lassgn le => Lassgn (leak_E lte le) 

  | LT_icond lte ltt ltf, Lcond le b lc => 
    Lcond (leak_E lte le) b(leak_C (if b then ltt else ltf) lc)

  | LT_iwhile ltc lte ltc', Lwhile_true lc le lc' lw => 
    Lwhile_true (leak_C ltc lc) (leak_E lte le) (leak_C ltc' lc') (leak_I lt lw)

  | LT_iwhile ltc lte ltc', Lwhile_false lc le => 
    Lwhile_false (leak_C ltc lc) (leak_E lte le)

  | LT_ifor lte ltc, Lfor le lcs => 
    Lfor (leak_E lte le) (leak_F ltc lcs) 

  | LT_icall lte lte', Lcall le (f, lc) le' => 
    Lcall (leak_E lte le) (f, (leak_C (leak_Fun f) lc)) (leak_E lte' le') 
  | _, _ => dummy_li (* Error *)
  end
with leak_F (lts:seq leak_c_tr) (lf:leak_for) : leak_for := 
  match lts, lf with
  | [::], [::]%LF => [::]
  | lt :: lts, (lc :: lf)%LF => leak_C lt lc :: leak_F lts lf
  | _, _ => [::] (* Error *)
  end.

Fixpoint wf_C (lt:leak_c_tr) (lc: leak_c) {struct lc} : bool :=
  wf_add (wf_body wf_I wf_C wf_F) lc lt

with wf_I (lt:leak_i_tr) (li : leak_i) {struct li} : bool :=
  match lt, li with
  | LT_ile lte, Lassgn le => wf_E lte le

  | LT_icond lte ltt ltf, Lcond le b lc => 
    wf_E lte le && wf_C (if b then ltt else ltf) lc

  | LT_iwhile ltc lte ltc', Lwhile_true lc le lc' lw => 
    wf_C ltc lc && wf_E lte le && wf_C ltc' lc' && wf_I lt lw

  | LT_iwhile ltc lte ltc', Lwhile_false lc le => 
    wf_C ltc lc && wf_E lte le

  | LT_ifor lte ltc, Lfor le lcs => 
    wf_E lte le && wf_F ltc lcs

  | LT_icall lte lte', Lcall le (f, lc) le' => 
    wf_E lte le && wf_C (leak_Fun f) lc && wf_E lte' le'
  | _, _ => false 
  end
with wf_F (lts:seq leak_c_tr) (lf:leak_for) : bool := 
  match lts, lf with
  | [::], [::]%LF => true 
  | lt::lts, (lc::lf)%LF => wf_C lt lc && wf_F lts lf
  | _, _ => false 
  end.

End Leak_I.

Definition leak_Fun (Fs: leak_f_tr) (f: funname) : leak_c_tr := odflt [::] (assoc Fs f).

Section Compose.

Context (compose_C : leak_c_tr -> leak_c_tr -> leak_c_tr * leak_c_tr).

Fixpoint compose_for lcs1 lc2 := 
  match lcs1 with
  | [::] => ([::], lc2)
  | lc1::lcs1 =>
    let lc := compose_C lc1 lc2 in
    let lcs := compose_for lcs1 lc.2 in
    (lc.1::lcs.1, lcs.2)
  end.

Context (compose_I : leak_i_tr -> leak_c_tr -> leak_c_tr * leak_c_tr) (li1:leak_i_tr).

Fixpoint compose_A  (lc2:leak_c_tr) : leak_c_tr * leak_c_tr :=
  match lc2 with
  | LT_iadd li :: lc2 => 
    let lc := compose_A lc2 in
    (LT_iadd li:: lc.1, lc.2)
  | _ => compose_I li1 lc2 
  end.

End Compose.

Print leak_i_tr.

(*Fixpoint compose_I (li1:leak_i_tr) (lc2:leak_c_tr) : leak_c_tr * leak_c_tr :=
  match lc2, li1 with
  | _, LT_iremove => ([:: LT_iremove], lc2)
  | _, LT_icond_eval b lcb =>
    let lc := compose_C lcb lc2 in
    ([:: LT_icond_eval b lc.1], lc.2)
  | _, LT_ifor_unroll lcs =>
    let lcs := compose_for lcs lc2 in
    ([:: LT_ifor_unroll lcs.1], lcs.2)

  | LT_iadd _ :: _, _ =>
    compose_A compose_I li1 lc2 

  | LT_iremove :: lc2, LT_iadd _ => ([::], lc2)
  | LT_iremove :: lc2, _         => ([:: LT_iremove], lc2)

  | LT_icond_eval b lc2b :: lc2, LT_icond _ lc1t lc1f => 
    let lcb := compose_C (if b then lc1t else lc1f) lc2b in
    (LT_icond_eval b lcb.1, lc2)

  | LT_icond_eval b lc2b :: lc2, LT_iwhile lc1w _ _ =>
    let lcb := compose_C lc1w lc2b in
    (LT_icond_eval b lcb.1, lc2)
 
  | LT_ifor_unroll lcs2 :: lc2, LT_ifor _ lcb1 =>
    let lcs := map (fun lc2 => (compose_C lcb1 lc2).1) lcs2 in
    ([::LT_ifor_unroll lcs], lc2)

  (* one to one *)
  
  | LT_ile le2 :: lc2, LT_ile le1 =>
    ([::LT_ile (compose_E le1 le2)], lc2)
  | LT_icond le2 lc2t lc2f :: lc2, LT_icond le1 lc1t lc1f  =>
    let lct := compose_C lc1t lc2t in
    let lcf := compose_C lc1f lc2f in
    let lc  := compose_C lc1  lc2  in
    (LT_icond (compose_E le1 le2) lct.1 lcf.1 :: lc.1, lc2)
*)
  

Fixpoint compose_C (lc1 lc2: leak_c_tr) : leak_c_tr * leak_c_tr :=
  match lc2, lc1 with
  (* Recursion on lc1 *)
  | _, [::] => ([::], lc2)
  | _, LT_iremove :: lc1 => 
    let lc := compose_C lc1 lc2 in
    (LT_iremove:: lc.1, lc.2)
  | _, LT_icond_eval b lc1b :: lc1 =>
    let lcb := compose_C lc1b lc2 in
    let lc  := compose_C lc1  lcb.2 in
    (LT_icond_eval b lcb.1, lc.2)
  | _, LT_ifor_unroll lcs1 :: lc1 =>
    let lcs := compose_for lcs1 lc1 lc2 in
    let lc  := compose_C lc1 lcs.2 in
    (LT_ifor_unroll lcs.1 :: lc.1, lc.2)

  (* Recusion on lc2, first leak_i_tr of lc1 correspond to an instruction *)
  | LT_iadd li :: lc2, _ =>
    let lc := compose_C lc1 lc2 in
    (LT_iadd li :: lc.1, lc.2)

  | LT_iremove :: lc2, LT_iadd _ :: lc1 => 
    compose_C lc1 lc2
  | LT_iremove :: lc2, _ :: lc1 => 
    let lc := compose_C lc1 lc2 in
    (LT_iremove :: lc.1, lc.2)
  | LT_icond_eval b lc2b :: lc2, LT_icond _ lc1t lc1f :: lc1 => 
    let lcb := compose_C (if b then lc1t else lc1f) lc2b in
    let lc  := compose_C lc1 lc2 in
    (LT_icond_eval b lcb.1 :: lc.1, lc.2)
  | LT_icond_eval b lc2b :: lc2, LT_iwhile lc1w _ _ :: lc1 =>
    let lcb := compose_C lc1w lc2b in
    let lc  := compose_C lc1 lc2 in
    (LT_icond_eval b lcb.1 :: lc.1, lc.2)
  | LT_ifor_unroll lcs2 :: lc2, LT_ifor _ lcb1 :: lc1 =>
    let lcs := map (fun lc2 => (compose_C lcb1 lc2).1) lcs2 in
    let lc  := compose_C lc1 lc2 in
    (LT_ifor_unroll lcs :: lc.1, lc.2)

  (* first leak_i_tr of lc1 and lc2 correspond to an instruction *)

  | LT_ile le2 :: lc2, LT_iadd le1 :: lc1 =>
    let lc := compose_C lc1 lc2 in
    (LT_iadd (leak_E le2 le1) :: lc.1, lc.2)

  | LT_ile le2 :: lc2, LT_ile le1 :: lc1 =>
    let lc := compose_C lc1 lc2 in
    (LT_ile (compose_e le1 le2) :: lc.1, lc.2)

  | LT_icond le2 lc2t lc2f :: lc2, LT_icond le1 lc1t lc1f :: lc1 =>
    let lct := compose_C lc1t lc2t in
    let lcf := compose_C lc1f lc2f in
    let lc  := compose_C lc1  lc2  in
    (LT_icond (compose_e le1 le2) lct.1 lcf.1 :: lc.1, lc.2)

  | LT_iwhile lc21 le2 lc22 :: lc2, LT_iwhile lc11 le1 lc12 :: lc1 =>
    let lc1 := compose_C lc11 lc21 in
    let lc2 := compose_C lc12 lc22 in
    let lc  := compose_C lc1 lc2 in
    (LT_iwhile lc1.1 (compose_e le1 le2) lc2.1 :: lc.1, lc.2)

  | LT_ifor le2 lcs2 :: lc2, LT_ifor le1 lcs1 :: lc1 =>
    let lcs := map (fun lc1 lc2 => (compose_C lc1 lc2).1) lcs1 lcs2 in
    let lc  := compose_C lc1 lc2 in
    (LT_ifor (compose_e le1 le2) lcs :: lc.1, lc.2)

  | LT_icall le21 le22 :: lc2, LT_icall le11 le12 :: lc1 =>
    let lc := compose_C lc1 lc2 in
    (LT_icall (compose_e le11 le21) (compose_e le12 le22) :: lc.1, lc.2)

  
  end.

     
....
*)

    

    
    




 


  match lc2, lc1 with
  | _ , [::] => [::], lc2
  | LT_iremove :: lc2, _ => compose_C (remove_lc lc1) lc2
  | _, LT_iremove :: lc1 => 
    let lc := compose_C lc1 lc2 in     
    (LT_iremove :: lc.1, lc.2)
  | LT_iadd li :: lc2, _ => 
    let lc := compose_C lc1 lc2 in     
    (LT_iadd li :: lc.1, lc.2)

  | LT_ile le2 :: lc2, LT_ile le1 :: lc1 => 
    let lc := compose_C lc1 lc2 in
    (LT_ile (compose_E le1 le2) lc.1, lc.2)

  | LT_icond le2 lc2t lc2f :: lc2, LT_icond le1 lc1t lc1f :: lc1 =>
    let lct := compose_C lc1t lc2t in
    let lcf := compose_C lc1f lc2f in
    let lc  := compose_C lc1  lc2  in
    (LT_icond (compose_E le1 le2) lct.1 lcf.1 :: lc.1, lc.2)

  | _, LT_icond_eval b lc1b :: lc1 => 
    let lcb := compose_C lc1b lc2 in
    let lc  := compose_C lc1  lcb.2
    (LT_icond_eval b lcb.1, lc.2)
  
  |
    

Fixpoint compose_C (lc1 lc2: leak_c_tr) : leak_c_tr * leac_c_tr :=
  match lc2, lc1 with
  | _ , [::] => [::], lc2
  | LT_iremove :: lc2, _ => compose_C (remove_lc lc1) lc2
  | _, LT_iremove :: lc1 => 
    let lc := compose_C lc1 lc2 in     
    (LT_iremove :: lc.1, lc.2)
  | LT_iadd li :: lc2, _ => 
    let lc := compose_C lc1 lc2 in     
    (LT_iadd li :: lc.1, lc.2)

  | LT_ile le2 :: lc2, LT_ile le1 :: lc1 => 
    let lc := compose_C lc1 lc2 in
    (LT_ile (compose_E le1 le2) lc.1, lc.2)

  | LT_icond le2 lc2t lc2f :: lc2, LT_icond le1 lc1t lc1f :: lc1 =>
    let lct := compose_C lc1t lc2t in
    let lcf := compose_C lc1f lc2f in
    let lc  := compose_C lc1  lc2  in
    (LT_icond (compose_E le1 le2) lct.1 lcf.1 :: lc.1, lc.2)

  | _, LT_icond_eval b lc1b :: lc1 => 
    let lcb := compose_C lc1b lc2 in
    let lc  := compose_C lc1  lcb.2
    (LT_icond_eval b lcb.1, lc.2)
  
  |
    

LT_icond le1 lc1t lc1f :: lc1 

Parameter compose_Fs : (funname → leak_c_tr) -> (funname → leak_c_tr) -> (funname → leak_c_tr).
Parameter compose_Is : leak_c_tr -> leak_c_tr -> leak_c_tr.

(*Axiom compose_Is0lt : forall lt2, (compose_Is [::] lt2) = [::].
Axiom compose_Islt0 : forall lt1, (compose_Is lt1 [::]) = [::].

Axiom composeIs_rmlt : forall lt1 lt2,
  compose_Is (LT_iremove :: lt1) lt2 = LT_iremove :: compose_Is lt1 lt2.    

(* Axiom composeIs_keeplt : forall lt1 t2 lt2,
  compose_Is (LT_ikeep :: lt1) (t2::lt2) = t2 :: compose_Is lt1 lt2.    *)

Lemma leak_I_rm Fs li : leak_I Fs li LT_iremove = [::].
Proof. by case: li. Qed.

(*Lemma leak_I_keep Fs li : leak_I Fs li LT_ikeep = [:: li].
Proof. by case: li. Qed. *)

Lemma leak_Is_cons F t lt li lc : leak_Is F (t::lt) (li::lc) = F li t ++ leak_Is F lt lc.
Proof. done. Qed.
(*
lt1 :: lt1s
 lt1  LT_ifor_unroll [l1; l2; l3]
lt2s
l1' ++ l2' ++ l3' ++ lt2s'
*)
*)

Section COMPOSE.

Context (Fs1 Fs2 : leak_f_tr).

Lemma compose_IP li foo Fs1 Fs2 lt1 lt2 lc :
  leak_C (leak_I Fs2) lt2 (leak_Is (leak_I Fs1) lt1 lc) =
    leak_Is (leak_I (compose_Fs Fs1 Fs2)) (compose_Is lt1 lt2) lc.
Proof.
  elim: lc lt1 lt2 => //.
  move=> li lc hrec.
  rewrite {2}/leak_Is /=.
  case => /=.
  + by move=> lt2; rewrite compose_Is0lt.
  case => /=.
  + move=> lt1 lt2; rewrite composeIs_rmlt /= leak_I_rm /=.
    by rewrite leak_Is_cons leak_I_rm hrec. 
  + move=> lt1 lt2.
    rewrite leak_I_keep.
    case: lt2. 
    + by rewrite compose_Islt0.
    move=> t2 lt2.
    rewrite composeIs_keeplt /leak_Is /=.
    f_equal; last by apply hrec.

admit.

    rewrite hrec.

axiom 

    rewrite 







