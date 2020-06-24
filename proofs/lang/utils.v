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
From Coq.Unicode Require Import Utf8.
Require Import ZArith Setoid Morphisms CMorphisms CRelationClasses.
Require Import xseq oseq.
Require Psatz.
From CoqWord Require Import ssrZ.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
Module FinIsCount.
Section FinIsCount.
Variable (T : eqType) (enum : seq T) (A : Finite.axiom enum).

Definition pickle (x : T) :=
  seq.index x enum.

Definition unpickle (n : nat) :=
  nth None [seq some x | x <- enum] n.

Definition pickleK : pcancel pickle unpickle.
Proof.
move=> x; have xE: x \in enum by apply/count_memPn; rewrite (A x).
by rewrite /pickle /unpickle (nth_map x) ?(nth_index, index_mem).
Qed.
End FinIsCount.
End FinIsCount.

(* ** Result monad
 * -------------------------------------------------------------------- *)

Variant result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

Definition is_ok (E A:Type) (r:result E A) := if r is Ok a then true else false.

Lemma is_ok_ok (E A:Type) (a:A) : is_ok (Ok E a).
Proof. done. Qed.
Hint Resolve is_ok_ok.

Lemma is_okP (E A:Type) (r:result E A) : reflect (exists (a:A), r = Ok E a) (is_ok r).
Proof.
  case: r => /=; constructor; first by eauto.
  by move=> [].
Qed.

Section ResultEqType.

Variable E A : eqType.

Definition result_eq (r1 r2: result E A): bool :=
  match r1, r2 with
  | Ok a1, Ok a2 => a1 == a2
  | Error e1, Error e2 => e1 == e2
  | _, _ => false
  end.

Lemma result_eqP : Equality.axiom result_eq.
Proof.
  case=> [a1|e1] [a2|e2] /=; try (by apply: ReflectF);
  by apply: (equivP eqP);split=>[|[]] ->.
Qed.

Canonical result_eqMixin := EqMixin result_eqP.
Canonical result_eqType := Eval hnf in EqType (result E A) result_eqMixin.

End ResultEqType.

Module Result.

Definition apply eT aT rT (f : aT -> rT) (x : rT) (u : result eT aT) :=
  if u is Ok y then f y else x.

Definition bind eT aT rT (f : aT -> result eT rT) g :=
  match g with
  | Ok x    => f x
  | Error s => Error s
  end.

Definition map eT aT rT (f : aT -> rT) := bind (fun x => Ok eT (f x)).
Definition default eT aT := @apply eT aT aT (fun x => x).

End Result.

Definition o2r eT aT (e : eT) (o : option aT) :=
  match o with
  | None   => Error e
  | Some x => Ok eT x
  end.

Notation rapp  := Result.apply.
Notation rdflt := Result.default.
Notation rbind := Result.bind.
Notation rmap  := Result.map.
Notation ok    := (@Ok _).

Notation "m >>= f" := (rbind f m) (at level 25, left associativity).
Notation "'Let' x ':=' m 'in' body" := (m >>= (fun x => body)) (at level 25).

Lemma bindA eT aT bT cT (f : aT -> result eT bT) (g: bT -> result eT cT) m:
  m >>= f >>= g = m >>= (fun a => f a >>= g).
Proof. case:m => //=. Qed.

Lemma bind_eq eT aT rT (f1 f2 : aT -> result eT rT) m1 m2 :
   m1 = m2 -> f1 =1 f2 -> m1 >>= f1 = m2 >>= f2.
Proof. move=> <- Hf; case m1 => //=. Qed.

Definition ok_inj {E A} (a a': A) (H: Ok E a = ok a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition Error_inj {E A} (a a': E) (H: @Error E A a = Error a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition assert E (b: bool) (e: E) : result E unit :=
  if b then ok tt else Error e.

Lemma assertP E b e u :
  @assert E b e = ok u → b.
Proof. by case: b. Qed.

Arguments assertP {E b e u} _.

Variant error :=
 | ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack | ErrType.

Scheme Equality for error.

Lemma error_beqP : Equality.axiom error_beq.
Proof.
  move=> e1 e2;case Heq: error_beq;constructor.
  + by apply: internal_error_dec_bl.
  by move=> /internal_error_dec_lb;rewrite Heq.
Qed.

Canonical error_eqMixin := EqMixin error_beqP.
Canonical error_eqType := Eval hnf in EqType error error_eqMixin.

Definition exec t := result error t.

Definition type_error {t} := @Error _ t ErrType.
Definition undef_error {t} := @Error error t ErrAddrUndef.

Lemma bindW {T U} (v : exec T) (f : T -> exec U) r :
  v >>= f = ok r -> exists2 a, v = ok a & f a = ok r.
Proof. by case E: v => [a|//] /= <-; exists a. Qed.

Lemma rbindP eT aT rT (e:result eT aT) (body:aT -> result eT rT) v (P:Type):
  (forall z, e = ok z -> body z = Ok _ v -> P) ->
  e >>= body = Ok _ v -> P.
Proof. by case: e=> //= a H /H H';apply H'. Qed.

Ltac t_rbindP := do? (apply: rbindP => ??).

Ltac t_xrbindP :=
  match goal with
  | [ |- Result.bind _ _ = Ok _ _ -> _ ] =>
      let y := fresh "y" in
      let h := fresh "h" in
      apply: rbindP=> y; t_xrbindP=> h;
      t_xrbindP; move: y h
  | [ |- ok _ = ok _ -> _ ] =>
      case; t_xrbindP
  | [ |- _ -> _ ] =>
      let h := fresh "h" in move=> h; t_xrbindP; move: h
  | _ => idtac
  end.

Ltac clarify :=
  repeat match goal with
  | H : ?a = ?b |- _ => subst a || subst b
  | H : ok _ = ok _ |- _ => apply ok_inj in H
  | H : Some _ = Some _ |- _ => move: H => /Some_inj H
  | H : ?a = _, K : ?a = _ |- _ => rewrite H in K
  end.

Lemma Let_Let {eT A B C} (a:result eT A) (b:A -> result eT B) (c: B -> result eT C) :
  ((a >>= b) >>= c) = a >>= (fun a => b a >>= c).
Proof. by case: a. Qed.

Definition mapM eT aT bT (f : aT -> result eT bT)  : seq aT → result eT (seq bT) :=
  fix mapM xs :=
  match xs with
  | [::] =>
      Ok eT [::]
  | [:: x & xs] =>
      f x >>= fun y =>
      mapM xs >>= fun ys =>
      Ok eT [:: y & ys]
  end.

Lemma mapM_cons aT eT bT x xs y ys (f : aT -> result eT bT):
  f x = ok y /\ mapM f xs = ok ys 
  <-> mapM f (x :: xs) = ok (y :: ys).
Proof.
  split.
  by move => [] /= -> ->.
  by simpl; t_xrbindP => y0 -> h0 -> -> ->.
Qed.

Lemma map_ext aT bT f g m :
  (forall a, List.In a m -> f a = g a) ->
  @map aT bT f m = map g m.
Proof.
elim: m => //= a m ih ext.
rewrite ext; [ f_equal | ]; eauto.
Qed.

Instance mapM_ext eT aT bT :
  Proper (@eqfun (result eT bT) aT ==> eq ==> eq) (@mapM eT aT bT).
Proof.
move => f g ext xs xs' <-{xs'}.
by elim: xs => //= a xs ->; rewrite (ext a); case: (g a).
Qed.

Lemma mapM_size eT aT bT f xs ys :
  @mapM eT aT bT f xs = ok ys ->
  size xs = size ys.
Proof.
elim: xs ys.
- by move => ys [<-].
move => x xs ih ys /=; case: (f _) => //= y.
by case: (mapM f xs) ih => //= ys' ih [] ?; subst; rewrite (ih _ erefl).
Qed.

Local Close Scope Z_scope.

Lemma mapM_nth eT aT bT f xs ys d d' n :
  @mapM eT aT bT f xs = ok ys ->
  n < size xs ->
  f (nth d xs n) = ok (nth d' ys n).
Proof.
elim: xs ys n.
- by move => ys n [<-].
move => x xs ih ys n /=; case h: (f _) => [ y | ] //=.
case: (mapM f xs) ih => //= ys' /(_ _ _ erefl) ih [] <- {ys}.
by case: n ih => // n /(_ n).
Qed.

Local Open Scope Z_scope.

Lemma mapM_onth eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n x :
  mapM f xs = ok ys →
  onth xs n = Some x →
  ∃ y, onth ys n = Some y ∧ f x = ok y.
Proof.
move => ok_ys.
case: (leqP (size xs) n) => hsz; first by rewrite (onth_default hsz).
elim: xs ys ok_ys n hsz.
- by move => ys [<-].
move => y xs ih ys' /=; t_xrbindP => z ok_z ys ok_ys <- [| n ] hsz /= ok_y.
- by exists z; case: ok_y => <-.
exact: (ih _ ok_ys n hsz ok_y).
Qed.

Lemma mapM_onth' eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n y :
  mapM f xs = ok ys →
  onth ys n = Some y →
  ∃ x, onth xs n = Some x ∧ f x = ok y.
Proof.
move => ok_ys.
case: (leqP (size ys) n) => hsz; first by rewrite (onth_default hsz).
elim: xs ys ok_ys n hsz.
- by move => ys [<-].
move => x xs ih ys' /=; t_xrbindP => z ok_z ys ok_ys <- [| n ] hsz /= ok_y.
- by exists x; case: ok_y => <-.
exact: (ih _ ok_ys n hsz ok_y).
Qed.

Lemma mapMP {eT} {aT bT: eqType} (f: aT -> result eT bT) (s: seq aT) (s': seq bT) y:
  mapM f s = ok s' ->
  reflect (exists2 x, x \in s & f x = ok y) (y \in s').
Proof.
elim: s s' => /= [s' [] <-|x s IHs s']; first by right; case.
apply: rbindP=> y0 Hy0.
apply: rbindP=> ys Hys []<-.
have IHs' := (IHs _ Hys).
rewrite /= in_cons eq_sym; case Hxy: (y0 == y).
  by left; exists x; [rewrite mem_head | rewrite -(eqP Hxy)].
apply: (iffP IHs')=> [[x' Hx' <-]|[x' Hx' Dy]].
  by exists x'; first by apply: predU1r.
rewrite -Dy.
case/predU1P: Hx'=> [Hx|].
+ exfalso.
  move: Hxy=> /negP Hxy.
  apply: Hxy.
  rewrite Hx Hy0 in Dy.
  by move: Dy=> [] ->.
+ by exists x'.
Qed.

Lemma mapM_In {aT bT eT} (f: aT -> result eT bT) (s: seq aT) (s': seq bT) x:
  mapM f s = ok s' ->
  List.In x s -> exists y, List.In y s' /\ f x = ok y.
Proof.
elim: s s'=> // a l /= IH s'.
apply: rbindP=> y Hy.
apply: rbindP=> ys Hys []<-.
case.
+ by move=> <-; exists y; split=> //; left.
+ move=> Hl; move: (IH _ Hys Hl)=> [y0 [Hy0 Hy0']].
  by exists y0; split=> //; right.
Qed.

Lemma mapM_In' {aT bT eT} (f: aT -> result eT bT) (s: seq aT) (s': seq bT) y:
  mapM f s = ok s' ->
  List.In y s' -> exists2 x, List.In x s & f x = ok y.
Proof.
elim: s s'.
+ by move => _ [<-].
move => a s ih s'' /=; t_xrbindP => b ok_b s' rec <- {s''} /=.
case.
+ by move=> <-; exists a => //; left.
by move => h; case: (ih _ rec h) => x hx ok_y; eauto.
Qed.

Section FOLDM.

  Context (eT aT bT:Type) (f:aT -> bT -> result eT bT).

  Fixpoint foldM (acc : bT) (l : seq aT) :=
    match l with
    | [::]         => Ok eT acc
    | [:: a & la ] => f a acc >>= fun acc => foldM acc la
    end.

  Definition isOk e a (r : result e a) :=
    if r is Ok _ then true else false.

End FOLDM.

Section FOLD2.

  Variable A B E R:Type.
  Variable e: E.
  Variable f : A -> B -> R -> result E R.

  Fixpoint fold2 (la:seq A) (lb: seq B) r :=
    match la, lb with
    | [::]  , [::]   => Ok E r
    | a::la, b::lb =>
      f a b r >>= (fold2 la lb)
    | _     , _      => Error e
    end.

End FOLD2.

Section MAP2.

  Variable A B E R:Type.
  Variable e: E.

  Variable f : A -> B -> result E R.

  Fixpoint mapM2 (la:seq A) (lb: seq B) :=
    match la, lb with
    | [::]  , [::]   => Ok E [::]
    | a::la, b::lb =>
      Let c := f a b in
      Let lc := mapM2 la lb in
      ok (c::lc)
    | _     , _      => Error e
    end.

  Lemma mapM2_Forall2 (P: R → B → Prop) ma mb mr :
    (∀ a b r, List.In (a, b) (zip ma mb) → f a b = ok r → P r b) →
    mapM2 ma mb = ok mr →
    List.Forall2 P mr mb.
  Proof.
    elim: ma mb mr.
    + move => [] // mr _ [<-]; constructor.
    move => a ma ih [] // b mb mr' h /=; t_xrbindP => r ok_r mr rec <- {mr'}.
    constructor.
    + by apply: (h _ _ _ _ ok_r); left.
    by apply: ih => // a' b' r' h' ok_r'; apply: (h a' b' r' _ ok_r'); right.
  Qed.

End MAP2.

(* Inversion lemmas *)
(* -------------------------------------------------------------- *)
Lemma seq_eq_injL A (m n: seq A) (h: m = n) :
  match m with
  | [::] => if n is [::] then True else False
  | a :: m' => if n is b :: n' then a = b ∧ m' = n' else False
  end.
Proof. by subst n; case: m. Qed.

Lemma List_Forall_inv A (P: A → Prop) m :
  List.Forall P m →
  match m with [::] => True | x :: m' => P x ∧ List.Forall P m' end.
Proof. by case. Qed.

Lemma List_Forall2_refl A (R:A->A->Prop) l : (forall a, R a a) -> List.Forall2 R l l.
Proof. by move=> HR;elim: l => // a l Hrec;constructor. Qed.

Lemma List_Forall2_inv_l A B (R: A → B → Prop) m n :
  List.Forall2 R m n →
  match m with
  | [::] => n = [::]
  | a :: m' => ∃ b n', n = b :: n' ∧ R a b ∧ List.Forall2 R m' n'
  end.
Proof. case; eauto. Qed.

Lemma List_Forall2_inv_r A B (R: A → B → Prop) m n :
  List.Forall2 R m n →
  match n with
  | [::] => m = [::]
  | b :: n' => ∃ a m', m = a :: m' ∧ R a b ∧ List.Forall2 R m' n'
  end.
Proof. case; eauto. Qed.

Section All2.

  Variable A B:Type.
  Variable f : A -> B -> bool.

  Fixpoint all2 (l1:seq A) (l2: seq B) :=
    match l1, l2 with
    | [::]  , [::]   => true
    | a1::l1, a2::l2 => f a1 a2 && all2 l1 l2
    | _     , _      => false
    end.

  Lemma all2P l1 l2 : reflect (List.Forall2 f l1 l2) (all2 l1 l2).
  Proof.
    elim: l1 l2 => [ | a l1 hrec] [ | b l2] /=;try constructor.
    + by constructor.
    + by move/List_Forall2_inv_l.
    + by move/List_Forall2_inv_r.
    apply: equivP;first apply /andP.
    split => [[]h1 /hrec h2 |];first by constructor.
    by case/List_Forall2_inv_l => b' [n] [] [-> ->] [->] /hrec.
  Qed.

End All2.

Section Map2.

  Context (A B C : Type) (f : A -> B -> C).

  Fixpoint map2 la lb :=
    match la, lb with
    | a::la, b::lb => f a b :: map2 la lb
    | _, _         => [::]
    end.

  Lemma map2E ma mb :
    map2 ma mb = map (λ ab, f ab.1 ab.2) (zip ma mb).
  Proof.
    elim: ma mb; first by case.
    by move => a ma ih [] // b mb /=; f_equal.
  Qed.

End Map2.

Section Map3.

  Context (A B C D : Type) (f : A -> B -> C -> D).

  Fixpoint map3 ma mb mc :=
    match ma, mb, mc with
    | a :: ma', b :: mb', c :: mc' => f a b c :: map3 ma' mb' mc'
    | _, _, _ => [::]
    end.

  Lemma map3E ma mb mc :
    map3 ma mb mc = map2 (λ ab, f ab.1 ab.2) (zip ma mb) mc.
  Proof.
    elim: ma mb mc; first by case.
    by move => a ma ih [] // b mb [] // c mc /=; f_equal.
  Qed.

End Map3.

(* ** Misc functions
 * -------------------------------------------------------------------- *)

Definition isSome aT (o : option aT) :=
  if o is Some _ then true else false.

Fixpoint list_to_rev (ub : nat) :=
  match ub with
  | O    => [::]
  | x.+1 => [:: x & list_to_rev x ]
  end.

Definition list_to ub := rev (list_to_rev ub).

Definition list_from_to (lb : nat) (ub : nat) :=
  map (fun x => x + lb)%nat (list_to (ub - lb)).

Definition conc_map aT bT (f : aT -> seq bT) (l : seq aT) :=
  flatten (map f l).

Definition oeq aT (f : aT -> aT -> Prop) (o1 o2 : option aT) :=
  match o1, o2 with
  | Some x1, Some x2 => f x1 x2
  | None,    None    => true
  | _ ,      _       => false
  end.

Definition req eT aT (f : aT -> aT -> Prop) (o1 o2 : result eT aT) :=
  match o1, o2 with
  | Ok x1,   Ok x2 => f x1 x2
  | Error _, Error _ => true
  | _ ,       _      => false
  end.

Lemma Forall2_trans (A B C:Type) l2 (R1:A->B->Prop) (R2:B->C->Prop)
                    l1 l3 (R3:A->C->Prop)  :
   (forall b a c, R1 a b -> R2 b c -> R3 a c) ->
   List.Forall2 R1 l1 l2 ->
   List.Forall2 R2 l2 l3 ->
   List.Forall2 R3 l1 l3.
Proof.
  move=> H hr1;elim: hr1 l3 => {l1 l2} [ | a b l1 l2 hr1 _ hrec] l3 /List_Forall2_inv_l.
  + by move => ->.
   by case => ? [?] [->] [??]; constructor; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Operators to build comparison                                              *)
(* ---------------------------------------------------------------------------*)

Section CTRANS.

  Definition ctrans c1 c2 := nosimpl (
    match c1, c2 with
    | Eq, _  => Some c2
    | _ , Eq => Some c1
    | Lt, Lt => Some Lt
    | Gt, Gt => Some Gt
    | _ , _  => None
    end).

  Lemma ctransI c : ctrans c c = Some c.
  Proof. by case: c. Qed.

  Lemma ctransC c1 c2 : ctrans c1 c2 = ctrans c2 c1.
  Proof. by case: c1 c2 => -[]. Qed.

  Lemma ctrans_Eq c1 c2 : ctrans Eq c1 = Some c2 <-> c1 = c2.
  Proof. by rewrite /ctrans;case:c1=> //=;split=>[[]|->]. Qed.

  Lemma ctrans_Lt c1 c2 : ctrans Lt c1 = Some c2 -> Lt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.

  Lemma ctrans_Gt c1 c2 : ctrans Gt c1 = Some c2 -> Gt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.

End CTRANS.

Notation Lex u v :=
  match u with
  | Lt => Lt
  | Eq => v
  | Gt => Gt
  end.

(* -------------------------------------------------------------------- *)

Scheme Equality for comparison.

Lemma comparison_beqP : Equality.axiom comparison_beq.
Proof.
  move=> e1 e2;case Heq: comparison_beq;constructor.
  + by apply: internal_comparison_dec_bl.
  by move=> /internal_comparison_dec_lb;rewrite Heq.
Qed.

Canonical comparison_eqMixin := EqMixin comparison_beqP.
Canonical comparison_eqType := Eval hnf in EqType comparison comparison_eqMixin.

(* -------------------------------------------------------------------- *)

Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall x y, cmp x y = Eq -> x = y;
  }.

Definition gcmp {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp} := cmp.

Section CMP.

  Context {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp}.

  Lemma cmp_trans y x z c:
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    by move=> H1 H2;apply (@cmp_ctrans _ _ C y);rewrite H1 H2 ctransI.
  Qed.

  Lemma cmp_refl x : cmp x x = Eq.
  Proof. by have := @cmp_sym _ _ C x x;case: (cmp x x). Qed.

  Definition cmp_lt x1 x2 := gcmp x1 x2 == Lt.

  Definition cmp_le x1 x2 := gcmp x2 x1 != Lt.

  Lemma cmp_le_refl x : cmp_le x x.
  Proof. by rewrite /cmp_le /gcmp cmp_refl. Qed.

  Lemma cmp_lt_trans y x z : cmp_lt x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_lt /gcmp => /eqP h1 /eqP h2;apply /eqP;apply (@cmp_ctrans _ _ C y).
    by rewrite h1 h2.
  Qed.

  Lemma cmp_le_trans y x z : cmp_le x y -> cmp_le y z -> cmp_le x z.
  Proof.
    rewrite /cmp_le /gcmp => h1 h2;have := (@cmp_ctrans _ _ C y z x).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_nle_lt x y: ~~ (cmp_le x y) = cmp_lt y x.
  Proof. by rewrite /cmp_le /cmp_lt /gcmp Bool.negb_involutive. Qed.

  Lemma cmp_nlt_le x y: ~~ (cmp_lt x y) = cmp_le y x.
  Proof. done. Qed.

  Lemma cmp_lt_le_trans y x z: cmp_lt x y -> cmp_le y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym z) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_le_lt_trans y x z: cmp_le x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym y) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_lt_le x y : cmp_lt x y -> cmp_le x y.
  Proof.
    rewrite /cmp_lt /cmp_le /gcmp => /eqP h.
    by rewrite cmp_sym h.
  Qed.

  Lemma cmp_nle_le x y : ~~ (cmp_le x y) -> cmp_le y x.
  Proof. by rewrite cmp_nle_lt; apply: cmp_lt_le. Qed.

End CMP.

Notation "m < n" := (cmp_lt m n) : cmp_scope.
Notation "m <= n" := (cmp_le m n) : cmp_scope.
Notation "m ≤ n" := (cmp_le m n) : cmp_scope.
Delimit Scope cmp_scope with CMP.

Hint Resolve cmp_le_refl.

Section EqCMP.

  Context {T:eqType} {cmp:T -> T -> comparison} {C:Cmp cmp}.

  Lemma cmp_le_eq_lt (s1 s2:T): cmp_le s1 s2 = cmp_lt s1 s2 || (s1 == s2).
  Proof.
    rewrite /cmp_le /cmp_lt cmp_sym /gcmp.
    case heq: cmp => //=.
    + by rewrite (cmp_eq heq) eqxx.
    case: eqP => // ?;subst.
    by rewrite cmp_refl in heq.
  Qed.

  Lemma cmp_le_antisym x y :
    cmp_le x y → cmp_le y x → x = y.
  Proof.
    by rewrite -cmp_nlt_le (cmp_le_eq_lt y) => /negbTE -> /eqP.
  Qed.

End EqCMP.

Section LEX.

  Variables (T1 T2:Type) (cmp1:T1 -> T1 -> comparison) (cmp2:T2 -> T2 -> comparison).

  Definition lex x y := Lex (cmp1 x.1 y.1) (cmp2 x.2 y.2).

  Lemma Lex_lex x1 x2 y1 y2 : Lex (cmp1 x1 y1) (cmp2 x2 y2) = lex (x1,x2) (y1,y2).
  Proof. done. Qed.

  Lemma lex_sym x y :
    cmp1 x.1 y.1 = CompOpp (cmp1 y.1 x.1) ->
    cmp2 x.2 y.2 = CompOpp (cmp2 y.2 x.2) ->
    lex  x y = CompOpp (lex  y x).
  Proof.
    by move=> H1 H2;rewrite /lex H1;case: cmp1=> //=;apply H2.
  Qed.

  Lemma lex_trans y x z:
    (forall c, ctrans (cmp1 x.1 y.1) (cmp1 y.1 z.1) = Some c -> cmp1 x.1 z.1 = c) ->
    (forall c, ctrans (cmp2 x.2 y.2) (cmp2 y.2 z.2) = Some c -> cmp2 x.2 z.2 = c) ->
    forall  c, ctrans (lex x y) (lex y z) = Some c -> lex x z = c.
  Proof.
    rewrite /lex=> Hr1 Hr2 c;case: cmp1 Hr1.
    + move=> H;rewrite (H (cmp1 y.1 z.1));last by rewrite ctrans_Eq.
      (case: cmp1;first by apply Hr2);
        rewrite ctransC; [apply ctrans_Lt | apply ctrans_Gt].
    + move=> H1 H2;rewrite (H1 Lt);move:H2;first by apply: ctrans_Lt.
      by case: cmp1.
    move=> H1 H2;rewrite (H1 Gt);move:H2;first by apply: ctrans_Gt.
    by case: cmp1.
  Qed.

  Lemma lex_eq x y :
    lex x y = Eq -> cmp1 x.1 y.1 = Eq /\ cmp2 x.2 y.2 = Eq.
  Proof.
    case: x y => [x1 x2] [y1 y2] /=.
    by rewrite /lex;case:cmp1 => //;case:cmp2.
  Qed.

  Instance LexO (C1:Cmp cmp1) (C2:Cmp cmp2) : Cmp lex.
  Proof.
    constructor=> [x y | y x z | x y].
    + by apply /lex_sym;apply /cmp_sym.
    + by apply /lex_trans;apply /cmp_ctrans.
    by case: x y => ?? [??] /lex_eq /= [] /(@cmp_eq _ _ C1) -> /(@cmp_eq _ _ C2) ->.
  Qed.

End LEX.

Section MIN.
  Context T (cmp: T → T → comparison) (O: Cmp cmp).
  Definition cmp_min (x y: T) : T :=
    if (x ≤ y)%CMP then x else y.

  Lemma cmp_minP x y (P: T → Prop) :
    ((x ≤ y)%CMP → P x) →
    ((y < x)%CMP → P y) →
    P (cmp_min x y).
  Proof.
    rewrite /cmp_min; case: ifP.
    - by move => _ /(_ erefl).
    by rewrite -cmp_nle_lt => -> _ /(_ erefl).
  Qed.

  Lemma cmp_min_leL x y :
    (cmp_min x y ≤ x)%CMP.
  Proof.
    apply: (@cmp_minP x y (λ z, z ≤ x)%CMP) => //.
    apply: cmp_lt_le.
  Qed.

  Lemma cmp_min_leR x y :
    (cmp_min x y ≤ y)%CMP.
  Proof. exact: (@cmp_minP x y (λ z, z ≤ y)%CMP). Qed.

  Lemma cmp_le_min x y :
    (x ≤ y)%CMP → cmp_min x y = x.
  Proof. by rewrite /cmp_min => ->. Qed.

End MIN.

Arguments cmp_min {T cmp O} x y.

Definition bool_cmp b1 b2 :=
  match b1, b2 with
  | false, true  => Lt
  | false, false => Eq
  | true , true  => Eq
  | true , false => Gt
  end.

Instance boolO : Cmp bool_cmp.
Proof.
  constructor=> [[] [] | [] [] [] c | [] []] //=; apply ctrans_Eq.
Qed.

Polymorphic Instance equiv_iffT: Equivalence iffT.
Proof.
  split.
  + by move=> x;split;apply id.
  + by move=> x1 x2 []??;split.
  move=> x1 x2 x3 [??] [??];constructor;auto.
Qed.

Polymorphic Instance subrelation_iff_arrow : subrelation iffT arrow.
Proof. by move=> ?? []. Qed.

Polymorphic Instance subrelation_iff_flip_arrow : subrelation iffT (flip arrow).
Proof. by move=> ?? []. Qed.

Instance reflect_m: Proper (iff ==> (@eq bool) ==> iffT) reflect.
Proof. by move=> P1 P2 Hiff b1 b2 ->; split=> H; apply (equivP H);rewrite Hiff. Qed.

Coercion Zpos : positive >-> Z.

Lemma P_leP (x y:positive) : reflect (x <= y)%Z (x <=? y)%positive.
Proof. apply: (@equivP (Pos.le x y)) => //;rewrite -Pos.leb_le;apply idP. Qed.

Lemma P_ltP (x y:positive) : reflect (x < y)%Z (x <? y)%positive.
Proof. apply: (@equivP (Pos.lt x y)) => //;rewrite -Pos.ltb_lt;apply idP. Qed.

Lemma Pos_leb_trans y x z:
  (x <=? y)%positive -> (y <=? z)%positive -> (x <=? z)%positive.
Proof. move=> /P_leP ? /P_leP ?;apply /P_leP;omega. Qed.

Lemma Pos_lt_leb_trans y x z:
  (x <? y)%positive -> (y <=? z)%positive -> (x <? z)%positive.
Proof. move=> /P_ltP ? /P_leP ?;apply /P_ltP;omega. Qed.

Lemma Pos_le_ltb_trans y x z:
  (x <=? y)%positive -> (y <? z)%positive -> (x <? z)%positive.
Proof. move=> /P_leP ? /P_ltP ?;apply /P_ltP;omega. Qed.

Lemma pos_eqP : Equality.axiom Pos.eqb.
Proof. by move=> p1 p2;apply:(iffP idP);rewrite -Pos.eqb_eq. Qed.

Definition pos_eqMixin := EqMixin pos_eqP.
Canonical  pos_eqType  := EqType positive pos_eqMixin.

Instance positiveO : Cmp Pos.compare.
Proof.
  constructor.
  + by move=> ??;rewrite Pos.compare_antisym.
  + move=> ????;case:Pos.compare_spec=> [->|H1|H1];
    case:Pos.compare_spec=> H2 //= -[] <- //;subst;
    rewrite ?Pos.compare_lt_iff ?Pos.compare_gt_iff //.
    + by apply: Pos.lt_trans H1 H2.
    by apply: Pos.lt_trans H2 H1.
  apply Pos.compare_eq.
Qed.

Lemma Z_eqP : Equality.axiom Z.eqb.
Proof. by move=> p1 p2;apply:(iffP idP);rewrite -Z.eqb_eq. Qed.

(*Definition Z_eqMixin := EqMixin Z_eqP.
Canonical  Z_eqType  := EqType Z Z_eqMixin. *)

Instance ZO : Cmp Z.compare.
Proof.
  constructor.
  + by move=> ??;rewrite Z.compare_antisym.
  + move=> ????;case:Z.compare_spec=> [->|H1|H1];
    case:Z.compare_spec=> H2 //= -[] <- //;subst;
    rewrite ?Z.compare_lt_iff ?Z.compare_gt_iff //.
    + by apply: Z.lt_trans H1 H2.
    by apply: Z.lt_trans H2 H1.
  apply Z.compare_eq.
Qed.

Lemma Z_to_nat_subn z1 z2 : 0 <= z1 -> 0 <= z2 -> z2 <= z1 ->
  Z.to_nat (z1 - z2) = (Z.to_nat z1 - Z.to_nat z2)%nat.
Proof.
case: z1 z2 => [|n1|n1] [|n2|n2] //=; try by rewrite /Z.le.
+ by move=> _ _ _; rewrite subn0.
move=> _ _; rewrite -[_ <= _]/(n2 <= n1)%positive => le.
have := Z.pos_sub_discr n1 n2; case: Z.pos_sub => /=.
+ by move=> ->; rewrite subnn.
+ move=> p ->; rewrite Pos2Nat.inj_add.
  by rewrite -[plus _ _]/(addn _ _) addnC addnK.
+ move=> p ->; apply/esym/eqP; rewrite subn_eq0.
  by rewrite Pos2Nat.inj_add leq_addr.
Qed.

Lemma Z_to_nat_le0 z : z <= 0 -> Z.to_nat z = 0%N.
Proof. by rewrite /Z.to_nat; case: z => //=; rewrite /Z.le. Qed.

(* ** Some Extra tactics
 * -------------------------------------------------------------------- *)

Ltac sinversion H := inversion H=>{H};subst.

(* -------------------------------------------------------------------- *)
Variant dup_spec (P : Prop) :=
| Dup of P & P.

Lemma dup (P : Prop) : P -> dup_spec P.
Proof. by move=> ?; split. Qed.

(* -------------------------------------------------------------------- *)
Lemma drop_add {T : Type} (s : seq T) (n m : nat) :
  drop n (drop m s) = drop (n+m) s.
Proof.
elim: s n m => // x s ih [|n] [|m] //;
  by rewrite !(drop0, drop_cons, addn0, addnS).
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_drop {T : Type} (s : seq T) (n m : nat) :
  (n <= size s)%nat -> (m <= size s)%nat -> drop n s = drop m s -> n = m.
Proof.
move => /leP hn /leP hm he; have := size_drop n s.
rewrite he size_drop /subn /subn_rec; Psatz.lia.
Qed.

Definition ZleP : ∀ x y, reflect (x <= y) (x <=? y) := Z.leb_spec0.
Definition ZltP : ∀ x y, reflect (x < y) (x <? y) := Z.ltb_spec0.

Lemma eq_dec_refl
           (T: Type) (dec: ∀ x y : T, { x = y } + { x ≠ y })
           (x: T) : dec x x = left erefl.
Proof.
case: (dec _ _) => // e; apply: f_equal.
exact: Eqdep_dec.UIP_dec.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma rwR1 (A:Type) (P:A->Prop) (f:A -> bool) :
  (forall a, reflect (P a) (f a)) ->
  forall a, (f a) <-> (P a).
Proof. by move=> h a; rewrite (rwP (h _)). Qed.

Lemma rwR2 (A B:Type) (P:A->B->Prop) (f:A -> B -> bool) :
  (forall a b, reflect (P a b) (f a b)) ->
  forall a b, (f a b) <-> (P a b).
Proof. by move=> h a b; rewrite (rwP (h _ _)). Qed.

Notation pify :=
  (rwR2 (@andP), rwR2 (@orP), rwR2 (@implyP), rwR1 (@forallP _), rwR1 (@negP)).

Notation zify := (pify, (rwR2 (@ZleP), rwR2 (@ZltP))).

(* -------------------------------------------------------------------- *)

Definition ziota p (z:Z) := [seq p + Z.of_nat i | i <- iota 0 (Z.to_nat z)].

Lemma ziota0 p : ziota p 0 = [::].
Proof. done. Qed.

Lemma ziota_neg p z: z <= 0 -> ziota p z = [::].
Proof. by case: z. Qed.

Lemma ziotaS_cons p z: 0 <= z -> ziota p (Z.succ z) = p :: ziota (p+1) z.
Proof.
  move=> hz;rewrite /ziota Z2Nat.inj_succ //= Z.add_0_r; f_equal.
  rewrite -addn1 addnC iota_addl -map_comp.
  by apply eq_map => i /=; rewrite Zpos_P_of_succ_nat;Psatz.lia.
Qed.

Lemma ziotaS_cat p z: 0 <= z -> ziota p (Z.succ z) = ziota p z ++ [:: p + z].
Proof.
  by move=> hz;rewrite /ziota Z2Nat.inj_succ // -addn1 iota_add map_cat /= add0n Z2Nat.id.
Qed.

Lemma in_ziota (p z i:Z) : (i \in ziota p z) = ((p <=? i) && (i <? p + z)).
Proof.
  case: (ZleP 0 z) => hz.
  + move: p; pattern z; apply natlike_ind => [ p | {z hz} z hz hrec p| //].
    + by rewrite ziota0 in_nil; case: andP => // -[/ZleP ? /ZltP ?]; Psatz.lia.
    rewrite ziotaS_cons // in_cons; case: eqP => [-> | ?] /=.
    + by rewrite Z.leb_refl /=; symmetry; apply /ZltP; Psatz.lia.
    by rewrite hrec; apply Bool.eq_iff_eq_true;split=> /andP [/ZleP ? /ZltP ?];
      (apply /andP;split;[apply /ZleP| apply /ZltP]); Psatz.lia.
  rewrite ziota_neg;last Psatz.lia.
  rewrite in_nil;symmetry;apply /negP => /andP [/ZleP ? /ZltP ?]; Psatz.lia.
Qed.

Lemma size_ziota p z: size (ziota p z) = Z.to_nat z.
Proof. by rewrite size_map size_iota. Qed.

Lemma nth_ziota p (i:nat) z : leq (S i) (Z.to_nat z) ->
   nth 0%Z (ziota p z) i = (p + Z.of_nat i)%Z.
Proof.
  by move=> hi;rewrite (nth_map O) ?size_iota // nth_iota.
Qed.

Lemma eq_map_ziota (T:Type) p1 p2 (f1 f2: Z -> T) :
  (forall i, (p1 <= i < p1 + p2)%Z -> f1 i = f2 i) ->
  map f1 (ziota p1 p2) = map f2 (ziota p1 p2).
Proof.
  move=> hi; have {hi}: (forall i, i \in ziota p1 p2 -> f1 i = f2 i).
  + move=> ?; rewrite in_ziota !zify; apply hi.
  elim: ziota => //= i l hrec hf; rewrite hrec;first by rewrite hf ?mem_head.
  by move=> ? hin; apply hf;rewrite in_cons hin orbT.
Qed.

Lemma all_ziota p1 p2 (f1 f2: Z -> bool) :
  (forall i, (p1 <= i < p1 + p2)%Z -> f1 i = f2 i) ->
  all f1 (ziota p1 p2) = all f2 (ziota p1 p2).
Proof.
  move=> hi; have {hi}: (forall i, i \in ziota p1 p2 -> f1 i = f2 i).
  + move=> ?; rewrite in_ziota !zify; apply hi.
  elim: ziota => //= i l hrec hf; rewrite hrec;first by rewrite hf ?mem_head.
  by move=> ? hin; apply hf;rewrite in_cons hin orbT.
Qed.


(* ------------------------------------------------------------------------- *)
Lemma sumbool_of_boolET (b: bool) (h: b) :
  Sumbool.sumbool_of_bool b = left h.
Proof. by move: h; rewrite /is_true => ?; subst. Qed.

Lemma sumbool_of_boolEF (b: bool) (h: b = false) :
  Sumbool.sumbool_of_bool b = right h.
Proof. by move: h; rewrite /is_true => ?; subst. Qed.

(* ------------------------------------------------------------------------- *)
Definition funname := positive.

Definition get_fundef {T} (p: seq (funname * T)) (f: funname) :=
  assoc p f.

(* ------------------------------------------------------------------------- *)

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Fixpoint ltuple (ts:list Type) : Type :=
  match ts with
  | [::]   => unit
  | [::t1] => t1
  | t1::ts => t1 * ltuple ts
  end.

Notation "(:: x , .. , y & z )" := (pair x .. (pair y z) ..) (only parsing).

Fixpoint merge_tuple (l1 l2: list Type) : ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2) :=
  match l1 return ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2) with
  | [::] => fun _ p => p
  | t1 :: l1 =>
    let rec := @merge_tuple l1 l2 in
    match l1 return (ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2)) ->
                    ltuple (t1::l1) -> ltuple l2 -> ltuple (t1 :: l1 ++ l2) with
    | [::] => fun _ (x:t1) =>
      match l2 return ltuple l2 -> ltuple (t1::l2) with
      | [::] => fun _ => x
      | t2::l2    => fun (p:ltuple (t2::l2)) => (x, p)
      end
    | t1' :: l1' => fun rec (x:t1 * ltuple (t1'::l1')) p =>
      (x.1, rec x.2 p)
    end rec
   end.
