(* * Utility definition for dmasm *)
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
Require Import ZArith Setoid Morphisms CMorphisms CRelationClasses.
Require Integers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ** Result monad
 * -------------------------------------------------------------------- *)

Variant result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

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

Inductive error := 
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

Fixpoint mapM eT aT bT (f : aT -> result eT bT) (xs : seq aT) : result eT (seq bT) :=
  match xs with
  | [::] =>
      Ok eT [::]
  | [:: x & xs] =>
      f x >>= fun y =>
      mapM f xs >>= fun ys =>
      Ok eT [:: y & ys]
  end.

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

Fixpoint foldM eT aT bT (f : aT -> bT -> result eT bT) (acc : bT) (l : seq aT) :=
  match l with
  | [::]         => Ok eT acc
  | [:: a & la ] => f a acc >>= fun acc => foldM f acc la
  end.

Definition isOk e a (r : result e a) :=
  if r is Ok _ then true else false.

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

Section All2.

  Variable A B:Type.
  Variable f : A -> B -> bool.
 
  Fixpoint all2 (l1:seq A) (l2: seq B) := 
    match l1, l2 with
    | [::]  , [::]   => true
    | a1::l1, a2::l2 => f a1 a2 && all2 l1 l2
    | _     , _      => false
    end.

End All2.

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

Lemma List_Forall2_refl A (R:A->A->Prop) l : (forall a, R a a) -> List.Forall2 R l l.
Proof. by move=> HR;elim: l => // a l Hrec;constructor. Qed.

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

Section LEX.

  Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall x y, cmp x y = Eq -> x = y;
  }.

  Lemma cmp_trans {T} {cmp} {C:@Cmp T cmp} y x z c:
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    by move=> H1 H2;apply (@cmp_ctrans _ _ C y);rewrite H1 H2 ctransI.
  Qed.

  Lemma cmp_refl  {T} {cmp} {C:@Cmp T cmp} x : cmp x x = Eq.
  Proof. by have := @cmp_sym _ _ C x x;case: (cmp x x). Qed.
 
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

Lemma P_leP x y : reflect (Zpos x <= Zpos y)%Z (x <=? y)%positive.
Proof. apply: (@equivP (Pos.le x y)) => //;rewrite -Pos.leb_le;apply idP. Qed.

Lemma P_ltP x y : reflect (Zpos x < Zpos y)%Z (x <? y)%positive.
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

Definition Z_eqMixin := EqMixin Z_eqP.
Canonical  Z_eqType  := EqType Z Z_eqMixin.

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

(* 64 bits word *)
Module I64 := Integers.Int64.

Definition i64_cmp (w1 w2:I64.int) := 
   Z.compare (I64.unsigned w1) (I64.unsigned w2).

Lemma i64_eqP : Equality.axiom (fun x y => I64.unsigned x == I64.unsigned y).
Proof.
  move=> p1 p2.
  have := I64.eq_spec p1 p2;rewrite /I64.eq /Coqlib.zeq.
  by case:Z.eq_dec => [/eqP | /eqP /negbTE] ->;constructor.
Qed.

Definition i64_eqMixin := EqMixin i64_eqP.
Canonical  i64_eqType  := EqType I64.int i64_eqMixin.

Lemma ueqP n1 n2: reflect (n1 = n2) (I64.unsigned n1 == I64.unsigned n2).
Proof. by apply (n1 =P n2). Qed.

Instance i64O : Cmp i64_cmp.
Proof.
  rewrite /i64_cmp;constructor.
  + by move=> ??;rewrite Z.compare_antisym. 
  + move=> ????;case:Z.compare_spec=> [->|H1|H1];
    case:Z.compare_spec=> H2 //= -[] <- //;
    rewrite -?H2 ?Z.compare_gt_iff ?Z.compare_lt_iff //.
    + move: (H2);rewrite -?Z.compare_lt_iff => ->.
      by rewrite Z.compare_lt_iff;apply: Z.lt_trans H1 H2. 
    by apply: Z.lt_trans H2 H1. 
  by move=> x y /Z.compare_eq Heq; rewrite -(I64.repr_unsigned x) -(I64.repr_unsigned y) Heq.
Qed.


(* ** Some Extra tactics
 * -------------------------------------------------------------------- *)

Ltac sinversion H := inversion H=>{H};subst.
