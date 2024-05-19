(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import fintype finfun.
From Coq.Unicode Require Import Utf8.
From Coq Require Import ZArith Zwf Setoid Morphisms CMorphisms CRelationClasses.
Require Import xseq oseq.
From mathcomp Require Import word_ssrZ.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

Lemma eq_axiom_of_scheme X (beq : X -> X -> bool) :
  (forall x y : X, beq x y -> x = y) ->
  (forall x y : X, x = y -> beq x y) ->
  Equality.axiom beq.
Proof. move=> hbl hlb x y. apply: (iffP idP); first exact: hbl. exact: hlb. Qed.

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

Class eqTypeC (T:Type) := 
  { beq : T -> T -> bool
  ; ceqP: Equality.axiom beq }.

Section EqType.

Context {T:Type} {ceqT : eqTypeC T}.
Definition ceqT_eqMixin := Equality.Mixin ceqP.
Definition ceqT_eqType  := Eval hnf in EqType T ceqT_eqMixin.

End EqType.

Notation "x == y ::> T" := (eq_op (T:= @ceqT_eqType T _) x y)
  (at level 70, y at next level) : bool_scope.

Notation "x == y ::>" := (eq_op (T:= @ceqT_eqType _ _) x y)
  (at level 70, y at next level) : bool_scope.

Class finTypeC (T:Type) :=
  { _eqC   : eqTypeC T
  ; cenum  : seq T
  ; cenumP : @Finite.axiom ceqT_eqType cenum
  }.

#[global]
Existing Instance _eqC.

Section FinType.

Context `{cfinT:finTypeC}.

Definition cfinT_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK cenumP).
Definition cfinT_choiceType :=
  Eval hnf in ChoiceType ceqT_eqType cfinT_choiceMixin.

Definition cfinT_countMixin :=
  PcanCountMixin (FinIsCount.pickleK cenumP).
Definition cfinT_countType :=
  Eval hnf in @Countable.pack T cfinT_countMixin cfinT_choiceType _ (fun x => x).

Definition cfinT_finMixin :=
  @Finite.EnumMixin cfinT_countType _ cenumP.
Definition cfinT_finType :=
  Eval hnf in 
    (@Finite.pack T ceqT_eqMixin cfinT_finMixin cfinT_choiceType _ (fun x => x) _ (fun x => x)).

Lemma mem_cenum : cenum =i ceqT_eqType.
Proof.
  move=> x. rewrite -has_pred1 has_count. by rewrite cenumP.
Qed.

End FinType.

Module FinMap.

Section Section.

Context `{cfinT:finTypeC} (U:Type).

(* Map from T -> U *)

Definition map := @finfun_of cfinT_finType (fun _ => U) (Phant _).

Definition of_fun := 
  @FinfunDef.finfun cfinT_finType (fun _ => U).

Definition set (m:map) (x: T) (y:U) : map := 
  of_fun (fun z : T => if z == x ::> then y else m z).

End Section.

End FinMap.

(* -------------------------------------------------------------------- *)
Lemma reflect_inj (T:eqType) (U:Type) (f:T -> U) a b : 
  injective f -> reflect (a = b) (a == b) -> reflect (f a = f b) (a == b).
Proof. by move=> hinj heq; apply: (iffP heq) => [| /hinj ] ->. Qed.

(* -------------------------------------------------------------------- *)
(* Missing Instance in ssreflect for setoid rewrite                     *)

#[global]
Instance and3_impl_morphism :
  Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and3 | 1.
Proof. by move=> ?? h1 ?? h2 ?? h3 [/h1 ? /h2 ? /h3 ?]. Qed.

#[global]
Instance and3_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> ?? h1 ?? h2 ?? h3; split => -[] /h1 ? /h2 ? /h3. Qed.

(* ** Result monad
 * -------------------------------------------------------------------- *)

Variant result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

Definition is_ok (E A:Type) (r:result E A) := if r is Ok a then true else false.

Lemma is_ok_ok (E A:Type) (a:A) : is_ok (Ok E a).
Proof. done. Qed.
#[global]
Hint Resolve is_ok_ok : core.

Lemma is_okP (E A:Type) (r:result E A) : reflect (exists (a:A), r = Ok E a) (is_ok r).
Proof.
  case: r => /=; constructor; first by eauto.
  by move=> [].
Qed.

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
Notation "'Let' x ':=' m 'in' body" := (m >>= (fun x => body)) (x name, at level 25).
Notation "'Let:' x ':=' m 'in' body" := (m >>= (fun x => body)) (x strict pattern, at level 25).
Notation "m >> n" := (rbind (λ _, n) m) (at level 30, right associativity, n at next level).

Lemma bindA eT aT bT cT (f : aT -> result eT bT) (g: bT -> result eT cT) m:
  m >>= f >>= g = m >>= (fun a => f a >>= g).
Proof. case:m => //=. Qed.

Lemma bind_eq eT aT rT (f1 f2 : aT -> result eT rT) m1 m2 :
   m1 = m2 -> f1 =1 f2 -> m1 >>= f1 = m2 >>= f2.
Proof. move=> <- Hf; case m1 => //=. Qed.

Definition ok_inj {E A} {a a': A} (H: Ok E a = ok a') : a = a' :=
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
 | ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack | ErrType | ErrArith.

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
      apply: rbindP; t_xrbindP
  | [ |- Result.map _ _ = Ok _ _ -> _ ] =>
      rewrite /rmap; t_xrbindP
  | [ |- assert _ _ = Ok _ _ -> _ ] =>
      move=> /assertP; t_xrbindP
  | [ |- unit -> _ ] =>
      case; t_xrbindP
  | [ |- ok _ = ok _ -> _ ] =>
      case; t_xrbindP
  | [ |- forall h, _ ] =>
      let hh := fresh h in move=> hh; t_xrbindP; move: hh
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

Lemma LetK {eT T} (r : result eT T) : Let x := r in ok x = r.
Proof. by case: r. Qed.

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

Lemma map_Forall2 aT bT (f : aT -> bT) m :
  List.Forall2 (fun a b => f a = b) m (map f m).
Proof. by elim: m => //= a m ih; constructor. Qed.

Lemma mapM_ext eT aT bT (f1 f2: aT → result eT bT) (m: seq aT) :
  (∀ a, List.In a m → f1 a = f2 a) →
  mapM f1 m = mapM f2 m.
Proof.
  elim: m => // a m ih ext /=.
  rewrite (ext a); last by left.
  case: (f2 _) => //= b; rewrite ih //.
  by move => ? h; apply: ext; right.
Qed.

Lemma eq_mapM eT (aT: eqType) bT (f1 f2: aT -> result eT bT) (l:list aT) :
  (forall a, a \in l -> f1 a = f2 a) ->
  mapM f1 l = mapM f2 l.
Proof.
  elim: l => //= a l hrec hf; rewrite hf ? hrec //.
  + by move=> ? h; apply/hf; rewrite in_cons h orbT.
  by apply mem_head.
Qed.

Lemma size_mapM eT aT bT f xs ys :
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

Lemma mapM_map {aT bT cT eT} (f: aT → bT) (g: bT → result eT cT) (xs: seq aT) :
  mapM g (map f xs) = mapM (g \o f) xs.
Proof. by elim: xs => // x xs ih /=; case: (g (f x)) => // y /=; rewrite ih. Qed.

Lemma mapM_cat  {eT aT bT} (f: aT → result eT bT) (s1 s2: seq aT) :
  mapM f (s1 ++ s2) = Let r1 := mapM f s1 in Let r2 := mapM f s2 in ok (r1 ++ r2).
Proof.
  elim: s1 s2; first by move => s /=; case (mapM f s).
  move => a s1 ih s2 /=.
  case: (f _) => // b; rewrite /= ih{ih}.
  case: (mapM f s1) => // bs /=.
  by case: (mapM f s2).
Qed.

Corollary mapM_rcons  {eT aT bT} (f: aT → result eT bT) (s: seq aT) (a: aT) :
  mapM f (rcons s a) = Let r1 := mapM f s in Let r2 := f a in ok (rcons r1 r2).
Proof. by rewrite -cats1 mapM_cat /=; case: (f a) => // b; case: (mapM _ _) => // bs; rewrite /= cats1. Qed.

Lemma mapM_Forall2 {eT aT bT} (f: aT → result eT bT) (s: seq aT) (s': seq bT) :
  mapM f s = ok s' →
  List.Forall2 (λ a b, f a = ok b) s s'.
Proof.
  elim: s s'.
  - by move => _ [] <-; constructor.
  move => a s ih s'' /=; t_xrbindP => b ok_b s' /ih{ih}ih <-{s''}.
  by constructor.
Qed.

Lemma mapM_factorization {aT bT cT eT fT} (f: aT → result fT bT) (g: aT → result eT cT) (h: bT → result eT cT) xs ys:
  (∀ a b, f a = ok b → g a = h b) →
  mapM f xs = ok ys →
  mapM g xs = mapM h ys.
Proof.
  move => E.
  elim: xs ys; first by case.
  by move => x xs ih ys' /=; t_xrbindP => y /E -> ys /ih -> <-.
Qed.

Lemma mapM_assoc {eT} {aT:eqType} {bT cT} (f : aT * bT -> result eT (aT * cT)) l1 l2 a b :
  (forall x y, f x = ok y -> x.1 = y.1) ->
  mapM f l1 = ok l2 ->
  assoc l1 a = Some b ->
  exists2 c, f (a, b) = ok (a, c) & assoc l2 a = Some c.
Proof.
  move=> hfst.
  elim: l1 l2 => //.
  move=> [a' b'] l1 ih /=.
  t_xrbindP=> _ [a'' c] h l2 /ih{ih}ih <- /=.
  have /= ? := hfst _ _ h; subst a''.
  case: eqP => [->|_]; last by apply ih.
  move=> [<-].
  by exists c.
Qed.

Lemma mapM_assoc' {eT} {aT:eqType} {bT cT} (f : aT * bT -> result eT (aT * cT)) l1 l2 a c :
  (forall x y, f x = ok y -> x.1 = y.1) ->
  mapM f l1 = ok l2 ->
  assoc l2 a = Some c ->
  exists2 b, f (a, b) = ok (a, c) & assoc l1 a = Some b.
Proof.
  move=> hfst.
  elim: l2 l1 => //.
  move=> [a' c'] l2 ih [//|[a'' b] l1] /=.
  t_xrbindP=> y h l2' hmap ??; subst y l2'.
  have /= ? := hfst _ _ h; subst a''.
  case: eqP => [->|_]; last by apply ih.
  move=> [<-].
  by exists b.
Qed.

Lemma mapM_take eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n :
  mapM f xs = ok ys →
  mapM f (take n xs) = ok (take n ys).
Proof.
  elim: xs ys n => [ | x xs hrec] ys n /=; first by move => /ok_inj<-.
  t_xrbindP => y hy ys' /hrec h ?; subst ys; case: n; first by rewrite take0.
  by move => n; rewrite /= (h n) /= hy.
Qed.

Lemma mapM_ok {eT} {A B:Type} (f: A -> B) (l:list A) :
  mapM (eT:=eT) (fun x => ok (f x)) l = ok (map f l).
Proof. by elim l => //= ?? ->. Qed.

Section FOLDM.

  Context (eT aT bT:Type) (f:aT -> bT -> result eT bT).

  Fixpoint foldM (acc : bT) (l : seq aT) :=
    match l with
    | [::]         => Ok eT acc
    | [:: a & la ] => f a acc >>= fun acc => foldM acc la
    end.

  Fixpoint foldrM (acc : bT) (l : seq aT) :=
    match l with
    | [::]         => Ok eT acc
    | [:: a & la ] => foldrM acc la >>= f a
    end.

  Lemma foldM_cat acc l1 l2 :
    foldM acc (l1 ++ l2) =
      Let acc1 := foldM acc l1 in
      foldM acc1 l2.
  Proof. by elim: l1 acc => //= x l hrec acc; case: f. Qed.

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

  Lemma size_fold2 xs ys x0 v:
    fold2 xs ys x0 = ok v -> size xs = size ys.
  Proof.
    by elim : xs ys x0 => [|x xs ih] [|y ys] x0 //= ; t_xrbindP => // t _ /ih ->.
  Qed.

  Lemma cat_fold2 ha ta hb tb x v v' :
    fold2 ha hb x = ok v -> fold2 ta tb v = ok v' ->
    fold2 (ha ++ ta) (hb ++ tb) x = ok v'.
  Proof.
    elim: ha hb x v => [[] // > [<-] | > hrec []] //= >.
    by t_xrbindP => ? -> /hrec{hrec}h/h{h}.
  Qed.

End FOLD2.

(* ---------------------------------------------------------------- *)
(* ALLM *)
Section ALLM.
  Context (A E: Type) (check: A → result E unit) (m: seq A).
  Definition allM := foldM (λ a _, check a) tt m.

  Lemma allMP a : List.In a m → allM = ok tt → check a = ok tt.
  Proof.
    rewrite /allM.
    by elim: m => // a' m' ih /= [ ->{a'} | /ih ]; t_xrbindP.
  Qed.

End ALLM.
Arguments allMP {A E check m a} _ _.

(* Forall3 *)
(* -------------------------------------------------------------- *)

Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Prop) : seq A -> seq B -> seq C -> Prop :=
| Forall3_nil : Forall3 R [::] [::] [::]
| Forall3_cons : forall a b c la lb lc, R a b c -> Forall3 R la lb lc -> Forall3 R (a :: la) (b :: lb) (c :: lc).

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

  Lemma size_mapM2 ma mb mr :
    mapM2 ma mb = ok mr ->
    size ma = size mb /\ size ma = size mr.
  Proof.
    elim: ma mb mr.
    + by move=> [|//] _ [<-].
    move=> a ma ih [//|b mb] /=.
    t_xrbindP=> _ r hf lr /ih{ih}ih <- /=.
    by Lia.lia.
  Qed.

  Lemma mapM2_Forall3 ma mb mr :
    mapM2 ma mb = ok mr ->
    Forall3 (fun a b r => f a b = ok r) ma mb mr.
  Proof.
    elim: ma mb mr.
    + by move=> [|//] [|//] _; constructor.
    move=> a ma ih [//|b mb] /=.
    t_xrbindP=> _ r h mr /ih{ih}ih <-.
    by constructor.
  Qed.

  Lemma mapM2_nth ma mb mr :
    mapM2 ma mb = ok mr ->
    forall a b r i,
      (i < size ma)%nat ->
      f (nth a ma i) (nth b mb i) = ok (nth r mr i).
  Proof.
    move=> H; elim: {H ma mb mr}(mapM2_Forall3 H) => //= a b r ma mb mr ok_r _ ih.
    by move=> a' b' r' [//|i]; apply ih.
  Qed.

  Lemma cat_mapM2 ha ta hb tb hl tl :
    mapM2 ha hb = ok hl -> mapM2 ta tb = ok tl ->
    mapM2 (ha ++ ta) (hb ++ tb) = ok (hl ++ tl).
  Proof.
    elim: ha hb hl => [[]//?[<-]|> hrec []] //=.
    by t_xrbindP=> > -> ? /hrec{hrec}hrec <- /hrec{hrec} ->.
  Qed.

End MAP2.

Section FMAP.

  Context (A B C:Type) (f : A -> B -> A * C).

  Fixpoint fmap (a:A) (bs:seq B) : A * seq C :=
    match bs with
    | [::] => (a, [::])
    | b::bs =>
      let (a, c) := f a b in
      let (a, cs) := fmap a bs in
      (a, c :: cs)
    end.

End FMAP.

Definition fmapM {eT aT bT cT} (f : aT -> bT -> result eT (aT * cT))  : aT -> seq bT -> result eT (aT * seq cT) :=
  fix mapM a xs :=
    match xs with
    | [::] => Ok eT (a, [::])
    | [:: x & xs] =>
      Let y := f a x in
      Let ys := mapM y.1 xs in
      Ok eT (ys.1, y.2 :: ys.2)
    end.

Definition fmapM2 {eT aT bT cT dT} (e:eT) (f : aT -> bT -> cT -> result eT (aT * dT)) : 
   aT -> seq bT -> seq cT -> result eT (aT * seq dT) :=
  fix mapM a lb lc :=
    match lb, lc with
    | [::], [::] => Ok eT (a, [::])
    | [:: b & bs], [:: c & cs] =>
      Let y := f a b c in
      Let ys := mapM y.1 bs cs in
      Ok eT (ys.1, y.2 :: ys.2)
    | _, _ => Error e
    end.

Lemma size_fmapM2 {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  size lb = size lc /\ size lb = size ld.
Proof.
  elim: lb lc a a2 ld.
  + by move=> [|//] _ _ _ [_ <-].
  move=> b lb ih [//|c lc] a /=.
  t_xrbindP=> _ _ _ _ [_ ld] /ih{ih}ih _ <- /=.
  by Lia.lia.
Qed.

Lemma fmapM2_split {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld i :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  exists a1,
    fmapM2 e f a (take i lb) (take i lc) = ok (a1, take i ld) /\
    fmapM2 e f a1 (drop i lb) (drop i lc) = ok (a2, drop i ld).
Proof.
  elim: lb lc a a2 ld i => [|b lb ih] [|c lc] //= a a2.
  + move=> _ _ [<- <-] /=.
    by eexists.
  t_xrbindP=> _ i [a1 d] /= h1 [{}a2 ld] h2 <- <-.
  case: i => [|i] /=.
  + eexists; split; first by reflexivity.
    by rewrite h1 /= h2.
  rewrite h1 /=.
  have [a1' [-> /= h2']] := ih _ _ _ _ i h2.
  by eexists; split; first by reflexivity.
Qed.

Lemma fmapM2_nth {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld i b c d :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  (i < size lb)%nat ->
  exists a1 a1',
    fmapM2 e f a (take i lb) (take i lc) = ok (a1, take i ld) /\
    f a1 (nth b lb i) (nth c lc i) = ok (a1', nth d ld i) /\
    fmapM2 e f a1' (drop i.+1 lb) (drop i.+1 lc) = ok (a2, drop i.+1 ld).
Proof.
  move=> hmap hi.
  have [a1 [hmap1 hmap2]] := fmapM2_split i hmap.
  have {hmap} [hsize1 hsize2] := size_fmapM2 hmap.
  move: hmap2.
  rewrite (drop_nth b hi).
  rewrite (drop_nth c); last by rewrite -hsize1.
  rewrite (drop_nth d) /=; last by rewrite -hsize2.
  t_xrbindP=> -[a1' d'] hf [a2' ld'] /= hmap2 ???; subst d' a2' ld'.
  by exists a1, a1'.
Qed.

(* Forall and size *)
(* -------------------------------------------------------------- *)

Lemma Forall2_size A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb -> size la = size lb.
Proof. by elim {la lb} => // a b la lb _ _ /= ->. Qed.

Lemma Forall3_size A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  size l1 = size l2 /\ size l1 = size l3.
Proof. by elim {l1 l2 l3} => // a b c l1 l2 l3 _ _ /= [<- <-]. Qed.

(* Reasoning with Forall *)
(* -------------------------------------------------------------- *)

Lemma Forall_nth A (R : A -> Prop) l :
  List.Forall R l ->
  forall d i, (i < size l)%nat -> R (nth d l i).
Proof.
  elim {l} => // a l h _ ih d [//|i].
  by apply ih.
Qed.

Lemma Forall2_nth A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall a b i, (i < size la)%nat ->
  R (nth a la i) (nth b lb i).
Proof.
  elim {la lb} => // a b la lb h _ ih a0 b0 [//|i].
  by apply ih.
Qed.

Lemma nth_Forall2 A B (R : A -> B -> Prop) la lb a b :
  size la = size lb ->
  (forall i : nat, (i < size la)%nat -> R (nth a la i) (nth b lb i)) ->
  List.Forall2 R la lb.
Proof.
  elim: la lb => [|a' la ih] [|b' lb] //= [] /ih{}ih hnth.
  constructor.
  + by apply (hnth 0%nat).
  by apply ih; move=> i; apply (hnth i.+1).
Qed.
Arguments nth_Forall2 [A B R la lb].

Lemma Forall2_forall A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall a b, List.In (a, b) (zip la lb) ->
  R a b.
Proof.
  elim {la lb} => // a b la lb h _ ih a0 b0 /=.
  case.
  + by move=> [<- <-].
  by apply ih.
Qed.

Lemma Forall2_impl A B (R1 R2 : A -> B -> Prop) :
  (forall a b, R1 a b -> R2 a b) ->
  forall la lb,
  List.Forall2 R1 la lb ->
  List.Forall2 R2 la lb.
Proof. by move=> himpl l1 l2; elim; eauto. Qed.

Lemma Forall2_impl_in A B (R1 R2 : A -> B -> Prop) la lb :
  (forall a b, List.In a la -> List.In b lb -> R1 a b -> R2 a b) ->
  List.Forall2 R1 la lb ->
  List.Forall2 R2 la lb.
Proof.
  move=> himpl hforall.
  elim: {la lb} hforall himpl.
  + by constructor.
  move=> a b la lb h _ ih himpl.
  constructor.
  + by apply himpl; [left; reflexivity..|].
  apply ih.
  by move=> ?????; apply himpl; [right..|].
Qed.

Lemma Forall2_flip A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  List.Forall2 (fun x y => R y x) lb la.
Proof. by elim {la lb} => // a b la lb h _ ih; constructor. Qed.

Lemma Forall2_take A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall n,
  List.Forall2 R (take n la) (take n lb).
Proof.
  elim {la lb} => //= a b la lb h _ ih n.
  case: n => [|n] //=.
  by constructor.
Qed.

Lemma Forall2_drop A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall n,
  List.Forall2 R (drop n la) (drop n lb).
Proof.
  elim {la lb} => //= a b la lb h ? ih n.
  case: n => [|n] //=.
  by constructor.
Qed.

Lemma Forall3_nth A B C (R : A -> B -> C -> Prop) la lb lc :
  Forall3 R la lb lc ->
  forall a b c i,
  (i < size la)%nat ->
  R (nth a la i) (nth b lb i) (nth c lc i).
Proof.
  elim {la lb lc} => // a b c la lb lc hr _ ih a0 b0 c0 [//|i].
  by apply ih.
Qed.

Lemma nth_Forall3 A B C (R : A -> B -> C -> Prop) la lb lc a b c:
  size la = size lb -> size la = size lc ->
  (forall i, (i < size la)%nat -> R (nth a la i) (nth b lb i) (nth c lc i)) ->
  Forall3 R la lb lc.
Proof.
  elim: la lb lc.
  + by move=> [|//] [|//] _ _ _; constructor.
  move=> a0 l1 ih [//|b0 l2] [//|c0 l3] [hsize1] [hsize2] h.
  constructor.
  + by apply (h 0%nat).
  apply ih => //.
  by move=> i; apply (h i.+1).
Qed.
Arguments nth_Forall3 [A B C R la lb lc].

Lemma Forall3_forall A B C (R : A -> B -> C -> Prop) la lb lc :
  Forall3 R la lb lc ->
  forall a b c, List.In (a, (b, c)) (zip la (zip lb lc)) -> R a b c.
Proof.
  elim {la lb lc} => // a b c la lb lc h _ ih a0 b0 c0 /=.
  case.
  + by move=> [<- <- <-].
  by apply ih.
Qed.

Lemma Forall3_impl A B C (R1 R2 : A -> B -> C -> Prop) :
  (forall a b c, R1 a b c -> R2 a b c) ->
  forall la lb lc,
  Forall3 R1 la lb lc ->
  Forall3 R2 la lb lc.
Proof. by move=> himpl l1 l2 l3; elim; eauto using Forall3. Qed.

Lemma Forall3_impl_in A B C (R1 R2 : A -> B -> C -> Prop) la lb lc :
  (forall a b c, List.In a la -> List.In b lb -> List.In c lc -> R1 a b c -> R2 a b c) ->
  Forall3 R1 la lb lc ->
  Forall3 R2 la lb lc.
Proof.
  move=> himpl hforall.
  elim: {la lb lc} hforall himpl.
  + by constructor.
  move=> a b c la lb lc h _ ih himpl.
  constructor.
  + by apply himpl; [left; reflexivity..|].
  apply ih.
  by move=> ???????; apply himpl; [right..|].
Qed.

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

Lemma List_Forall2_inv A B (R: A → B → Prop) m n :
  List.Forall2 R m n →
  if m is a :: m' then if n is b :: n' then R a b ∧ List.Forall2 R m' n' else False else if n is [::] then True else False.
Proof. case; auto. Qed.

Lemma List_Forall3_inv A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  match l1, l2, l3 with
  | [::], [::], [::] => True
  | a :: l1, b :: l2, c :: l3 => R a b c /\ Forall3 R l1 l2 l3
  | _, _, _ => False
  end.
Proof. by case. Qed.

(* Transitivity of Forall *)
(* -------------------------------------------------------------- *)

Lemma Forall2_trans A B C lb (R1:A->B->Prop) (R2:B->C->Prop)
                    la lc (R3:A->C->Prop) :
  (forall b a c, R1 a b -> R2 b c -> R3 a c) ->
  List.Forall2 R1 la lb ->
  List.Forall2 R2 lb lc ->
  List.Forall2 R3 la lc.
Proof.
  move=> himpl hfor1.
  elim: {la lb} hfor1 lc => [ | a b la lb hr1 _ hrec] + /List_Forall2_inv_l.
  + by move=> _ ->.
  by move=> _ [c [lc [-> [hr2 hfor2]]]]; constructor; eauto.
Qed.

Section Subseq.

  Context (T : eqType).
  Context (p : T -> bool).

  Lemma subseq_has s1 s2 : subseq s1 s2 -> has p s1 -> has p s2.
  Proof.
    move=> /mem_subseq hsub /hasP [x /hsub hin hp].
    apply /hasP.
    by exists x.
  Qed.

  Lemma subseq_all s1 s2 : subseq s1 s2 -> all p s2 -> all p s1.
  Proof.
    move=> /mem_subseq hsub /allP hall.
    by apply /allP => x /hsub /hall.
  Qed.

End Subseq.

Section All2.

Section DifferentTypes.

  Context (S T : Type).
  Context (p : S -> T -> bool).

  Lemma all2P l1 l2 : reflect (List.Forall2 p l1 l2) (all2 p l1 l2).
  Proof.
    elim: l1 l2 => [ | a l1 hrec] [ | b l2] /=;try constructor.
    + by constructor.
    + by move/List_Forall2_inv_l.
    + by move/List_Forall2_inv_r.
    apply: equivP;first apply /andP.
    split => [[]h1 /hrec h2 |];first by constructor.
    by case/List_Forall2_inv_l => b' [n] [] [-> ->] [->] /hrec.
  Qed.

  Section Ind.

    Context (P : list S -> list T -> Prop).

    Lemma list_all2_ind :
      P [::] [::] ->
      (forall x1 l1 x2 l2, p x1 x2 -> all2 p l1 l2 -> P l1 l2 -> P (x1::l1) (x2::l2)) ->
      forall l1 l2, all2 p l1 l2 -> P l1 l2.
    Proof.
      move=> hnil hcons; elim => /=; first by case.
      move=> x1 l1 ih [//|x2 l2] /andP [hf hall2].
      by apply hcons => //; apply ih.
    Qed.

  End Ind.

  Lemma all2_nth s t n ss ts :
    (n < size ss)%nat || (n < size ts)%nat ->
    all2 p ss ts ->
    p (nth s ss n) (nth t ts n).
  Proof.
    move=> hn; rewrite all2E => /andP [] /eqP hsz.
    move: hn; rewrite -hsz orbb => hn.
    move=> /(all_nthP (s, t)) -/(_ n).
    by rewrite size_zip -hsz minnn nth_zip //; apply.
  Qed.

  Lemma all2_map S' T' (f:S'->S) (g:T'->T) l1 l2 :
    all2 (fun x y => p (f x) (g y)) l1 l2 = all2 p (map f l1) (map g l2).
  Proof.
    elim: l1 l2 => [|x1 l1 ih] [|x2 l2] //=.
    by rewrite ih.
  Qed.

End DifferentTypes.

Section SameType.

  Context (T : Type).

  Section AnyRelation.

    Context (p : rel T).

    Lemma all2_refl : ssrbool.reflexive p -> ssrbool.reflexive (all2 p).
    Proof.
      move=> hrefl.
      by elim=> //= a l ih; apply /andP.
    Qed.

    Lemma all2_trans : ssrbool.transitive p -> ssrbool.transitive (all2 p).
    Proof.
      move=> htrans s1 s2 s3 hall2; move: hall2 s3.
      elim/list_all2_ind {s1 s2} => //= x1 s1 x2 s2 hp12 _ ih [//|x3 s3] /andP [hp23 hall2].
      by apply /andP; eauto.
    Qed.

  End AnyRelation.

  Section Eqb.

    Variable eqb: T -> T -> bool.
    Variable Heq : forall (x y:T), reflect (x = y) (eqb x y).

    Lemma reflect_all2_eqb l1 l2 : reflect (l1 = l2) (all2 eqb l1 l2).
    Proof.
      elim: l1 l2 => [|e1 l1 Hrec1] [|e2 l2] /=; try by constructor.
      by apply (iffP andP) => -[] /Heq -> /Hrec1 ->.
    Defined.

  End Eqb.

End SameType.

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

Section MAPI.

  Context (A : Type) (a : A) (B:Type) (b : B) (f : nat -> A -> B).

  Fixpoint mapi_aux k l :=
    match l with
    | [::] => [::]
    | a::l=> f k a :: mapi_aux k.+1 l
    end.

  Definition mapi := mapi_aux 0.

  Lemma size_mapi_aux k l : size (mapi_aux k l) = size l.
  Proof.
    elim: l k => //= a' l ih k.
    by rewrite ih.
  Qed.

  Lemma size_mapi l : size (mapi l) = size l.
  Proof. exact: size_mapi_aux. Qed.

  Lemma nth_mapi_aux n k l :
    (n < size l)%nat -> nth b (mapi_aux k l) n = f (k+n) (nth a l n).
  Proof.
    elim: l n k => //= a' l ih n k hlt.
    case: n hlt => /=.
    + by move=> _; rewrite addn0.
    by move=> n hlt; rewrite ih // addSnnS.
  Qed.

  Lemma nth_mapi n l :
    (n < size l)%nat -> nth b (mapi l) n = f n (nth a l n).
  Proof. exact: nth_mapi_aux. Qed.

End MAPI.

Section FIND_MAP.

(* The name comes from OCaml. *)
Fixpoint find_map {A B: Type} (f: A → option B) l :=
  match l with
  | [::] => None
  | a::l =>
    let fa := f a in
    if fa is None then find_map f l else fa
  end.

Lemma find_map_correct {A: eqType} {B: Type} {f: A → option B} {l b} :
  find_map f l = Some b -> exists2 a, a \in l & f a = Some b.
Proof.
  elim: l => //= a l ih.
  case heq: (f a) => [b'|].
  + by move=> [<-]; exists a => //; rewrite mem_head.
  move=> /ih [a' h1 h2]; exists a'=> //.
  by rewrite in_cons; apply /orP; right.
Qed.

End FIND_MAP.

(* ** Misc functions
 * -------------------------------------------------------------------- *)

Lemma isSome_obind (aT bT: Type) (f: aT → option bT) (o: option aT) :
  reflect (exists2 a, o = Some a & isSome (f a)) (isSome (o >>= f)%O).
Proof.
  apply: Bool.iff_reflect; split.
  - by case => a ->.
  by case: o => // a h; exists a.
Qed.

Lemma isSome_omap aT bT (f : aT -> bT) (o : option aT) :
  isSome (Option.map f o) = isSome o.
Proof. by case: o. Qed.

Fixpoint list_to_rev (ub : nat) :=
  match ub with
  | O    => [::]
  | x.+1 => [:: x & list_to_rev x ]
  end.

Definition list_to ub := rev (list_to_rev ub).

(* is it not just List.flat_map? *)
Definition conc_map aT bT (f : aT -> seq bT) (l : seq aT) :=
  flatten (map f l).

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
  exact:
    (eq_axiom_of_scheme internal_comparison_dec_bl internal_comparison_dec_lb).
Qed.

Canonical comparison_eqMixin := EqMixin comparison_beqP.
Canonical comparison_eqType := Eval hnf in EqType comparison comparison_eqMixin.

(* -------------------------------------------------------------------- *)

Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall {x y}, cmp x y = Eq -> x = y;
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

Declare Scope cmp_scope.
Notation "m < n" := (cmp_lt m n) : cmp_scope.
Notation "m <= n" := (cmp_le m n) : cmp_scope.
Notation "m ≤ n" := (cmp_le m n) : cmp_scope.
Delimit Scope cmp_scope with CMP.

#[global]
Hint Resolve cmp_le_refl : core.

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

  Lemma LexO (C1:Cmp cmp1) (C2:Cmp cmp2) : Cmp lex.
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

Section MAX.
  Context T (cmp: T → T → comparison) (O: Cmp cmp).
  Definition cmp_max (x y: T) : T :=
    if (x ≤ y)%CMP then y else x.

  Lemma cmp_maxP x y (P: T → Prop) :
    ((x ≤ y)%CMP → P y) →
    ((y < x)%CMP → P x) →
    P (cmp_max x y).
  Proof.
    rewrite /cmp_max; case: ifP.
    - by move => _ /(_ erefl).
    by rewrite -cmp_nle_lt => -> _ /(_ erefl).
  Qed.

  Lemma cmp_max_geL x y :
    (x <= cmp_max x y)%CMP.
  Proof. exact: (@cmp_maxP x y (λ z, x ≤ z)%CMP). Qed.

  Lemma cmp_max_geR x y :
    (y <= cmp_max x y)%CMP.
  Proof.
    apply: (@cmp_maxP x y (λ z, y ≤ z)%CMP) => //.
    apply: cmp_lt_le.
  Qed.

  Lemma cmp_le_max x y :
    (x ≤ y)%CMP → cmp_max x y = y.
  Proof. by rewrite /cmp_max => ->. Qed.

End MAX.

Arguments cmp_max {T cmp O} x y.

Definition bool_cmp b1 b2 :=
  match b1, b2 with
  | false, true  => Lt
  | false, false => Eq
  | true , true  => Eq
  | true , false => Gt
  end.

#[global]
Instance boolO : Cmp bool_cmp.
Proof.
  constructor=> [[] [] | [] [] [] c | [] []] //=; apply ctrans_Eq.
Qed.

#[global]
Polymorphic Instance subrelation_iff_flip_arrow : subrelation iffT (flip arrow).
Proof. by move=> ?? []. Qed.

#[global]
Instance reflect_m: Proper (iff ==> (@eq bool) ==> iffT) reflect.
Proof. by move=> P1 P2 Hiff b1 b2 ->; split=> H; apply (equivP H);rewrite Hiff. Qed.

Coercion Zpos : positive >-> Z.

Lemma P_leP (x y:positive) : reflect (x <= y)%Z (x <=? y)%positive.
Proof. apply: (@equivP (Pos.le x y)) => //;rewrite -Pos.leb_le;apply idP. Qed.

Lemma P_ltP (x y:positive) : reflect (x < y)%Z (x <? y)%positive.
Proof. apply: (@equivP (Pos.lt x y)) => //;rewrite -Pos.ltb_lt;apply idP. Qed.

Lemma Pos_leb_trans y x z:
  (x <=? y)%positive -> (y <=? z)%positive -> (x <=? z)%positive.
Proof. move=> /P_leP ? /P_leP ?;apply /P_leP; Lia.lia. Qed.

Lemma Pos_lt_leb_trans y x z:
  (x <? y)%positive -> (y <=? z)%positive -> (x <? z)%positive.
Proof. move=> /P_ltP ? /P_leP ?;apply /P_ltP; Lia.lia. Qed.

Lemma pos_eqP : Equality.axiom Pos.eqb.
Proof. by move=> p1 p2;apply:(iffP idP);rewrite -Pos.eqb_eq. Qed.

Definition pos_eqMixin := EqMixin pos_eqP.
Canonical  pos_eqType  := EqType positive pos_eqMixin.

#[global]
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

#[global]
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

Lemma Z_to_nat_le0 z : z <= 0 -> Z.to_nat z = 0%N.
Proof. by rewrite /Z.to_nat; case: z => //=; rewrite /Z.le. Qed.

Lemma Z_odd_pow_2 n x :
  (0 < n)%Z
  -> Z.odd (2 ^ n * x) = false.
Proof.
  move=> hn.
  rewrite Z.odd_mul.
  by rewrite (Z.odd_pow _ _ hn).
Qed.

(* ** Some Extra tactics
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Variant dup_spec (P : Prop) :=
| Dup of P & P.

Lemma dup (P : Prop) : P -> dup_spec P.
Proof. by move=> ?; split. Qed.

(* -------------------------------------------------------------------- *)
Definition ZleP : ∀ x y, reflect (x <= y) (x <=? y) := Z.leb_spec0.
Definition ZltP : ∀ x y, reflect (x < y) (x <? y) := Z.ltb_spec0.

(* -------------------------------------------------------------------- *)
Section NAT.

Open Scope nat.

Lemma ZNleP x y :
  reflect (Z.of_nat x <= Z.of_nat y)%Z (x <= y).
Proof.
  case h: (x <= y).
  all: move: h => /leP /Nat2Z.inj_le.
  all: by constructor.
Qed.

Lemma ZNltP x y :
  reflect (Z.of_nat x < Z.of_nat y)%Z (x < y).
Proof.
  case h: (x < y).
  all: move: h => /ZNleP.
  all: rewrite Nat2Z.inj_succ.
  all: move=> /Z.le_succ_l.
  all: by constructor.
Qed.

Lemma lt_nm_n n m :
  n + m < n = false.
Proof.
  rewrite -{2}(addn0 n).
  rewrite ltn_add2l.
  exact: ltn0.
Qed.

Lemma sub_nmn n m :
  n + m - n = m.
Proof.
  elim: n => //.
  by rewrite add0n subn0.
Qed.

End NAT.

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

Lemma Zcmp_le i1 i2 : (i1 <= i2)%CMP = (i1 <=? i2)%Z.
Proof.
  rewrite /cmp_le /gcmp /Z.leb -Zcompare_antisym.
  by case: Z.compare.
Qed.

Lemma Zcmp_lt i1 i2 : (i1 < i2)%CMP = (i1 <? i2)%Z.
Proof.
  rewrite /cmp_lt /gcmp /Z.ltb.
  by case: Z.compare.
Qed.

Notation zify := (Zcmp_le, Zcmp_lt, pify, (rwR2 (@ZleP), rwR2 (@ZltP))).

(* -------------------------------------------------------------------- *)

Definition Zwf0_pred_t x : Prop :=
  if x is Zpos p
  then 0 <= Zpos p ∧ Z.pred (Zpos p) < Zpos p
  else True.

Lemma Zwf0_pred x : Zwf0_pred_t x.
Proof. case: x => // p; red; Lia.lia. Qed.

Fixpoint ziota_rec (first z: Z) (H: Acc (Zwf 0) z) : seq Z :=
  let: Acc_intro REC := H in
  match z as z' return (∀ x : Z, Zwf 0 x z' → @Acc Z (Zwf 0) x) -> Zwf0_pred_t z' -> seq Z with
  | Zpos p => λ REC h, first :: ziota_rec (Z.succ first) (REC (Z.pred p) h)
  | _ => λ _ _, [::]
  end REC (Zwf0_pred z).

Definition ziota p z : seq Z :=
  ziota_rec p (Acc_intro_generator 2 (Zwf_well_founded 0) z).

Fixpoint ziota_recP p z H :
  @ziota_rec p z H = [seq p + Z.of_nat i | i <- iota 0 (Z.to_nat z)].
Proof.
  case: H => REC.
  rewrite /ziota_rec.
  case: z REC => // z' REC.
  rewrite -/(@ziota_rec (Z.succ p) (Z.pred z')).
  have -> : Z.to_nat z' = (Z.to_nat (Z.pred z')).+1 by Lia.lia.
  rewrite map_cons -/(iota _ _) Z.add_0_r; congr (_ :: _).
  rewrite (iotaDl 1) -map_comp.
  rewrite ziota_recP.
  apply: eq_map => i /=.
  Lia.lia.
Qed.

Lemma ziotaE p z :
  ziota p z = [seq p + Z.of_nat i | i <- iota 0 (Z.to_nat z)].
Proof. exact: ziota_recP. Qed.

Lemma ziota0 p : ziota p 0 = [::].
Proof. done. Qed.

Lemma ziota_neg p z: z <= 0 -> ziota p z = [::].
Proof. by case: z. Qed.

Lemma ziotaS_cons p z: 0 <= z -> ziota p (Z.succ z) = p :: ziota (p+1) z.
Proof.
  rewrite !ziotaE.
  move=> hz;rewrite /ziota Z2Nat.inj_succ //= Z.add_0_r; f_equal.
  rewrite -addn1 addnC iotaDl -map_comp.
  by apply eq_map => i /=; rewrite Zpos_P_of_succ_nat; Lia.lia.
Qed.

Lemma ziotaS_cat p z: 0 <= z -> ziota p (Z.succ z) = ziota p z ++ [:: p + z].
Proof.
  rewrite !ziotaE.
  by move=> hz;rewrite Z2Nat.inj_succ // -addn1 iotaD map_cat /= add0n Z2Nat.id.
Qed.

Lemma ziota_cat p y z: 0 <= y -> 0 <= z ->
  ziota p y ++ ziota (p + y) z = ziota p (y + z).
Proof.
  move=> ? /Z2Nat.id <-; elim: (Z.to_nat _).
  + by rewrite Z.add_0_r /= cats0.
  move=> ? hrw; rewrite Nat2Z.inj_succ Z.add_succ_r !ziotaS_cat; last 2 first.
  + exact: (Ztac.add_le _ _ _ (Zle_0_nat _)).
  + exact: Zle_0_nat.
  by rewrite catA hrw Z.add_assoc.
Qed.

Lemma in_ziota (p z i:Z) : (i \in ziota p z) = ((p <=? i) && (i <? p + z)).
Proof.
  case: (ZleP 0 z) => hz.
  + move: p; pattern z; apply natlike_ind => [ p | {z hz} z hz hrec p| //].
    + by rewrite ziota0 in_nil; case: andP => // -[/ZleP ? /ZltP ?]; Lia.lia.
    rewrite ziotaS_cons // in_cons; case: eqP => [-> | ?] /=.
    + by rewrite Z.leb_refl /=; symmetry; apply /ZltP; Lia.lia.
    by rewrite hrec; apply Bool.eq_iff_eq_true;split=> /andP [/ZleP ? /ZltP ?];
      (apply /andP;split;[apply /ZleP| apply /ZltP]); Lia.lia.
  rewrite ziota_neg;last Lia.lia.
  rewrite in_nil;symmetry;apply /negP => /andP [/ZleP ? /ZltP ?]; Lia.lia.
Qed.

Lemma size_ziota p z: size (ziota p z) = Z.to_nat z.
Proof. by rewrite ziotaE size_map size_iota. Qed.

Lemma nth_ziota p (i:nat) z : leq (S i) (Z.to_nat z) ->
   nth 0%Z (ziota p z) i = (p + Z.of_nat i)%Z.
Proof.
  by move=> hi; rewrite ziotaE (nth_map O) ?size_iota // nth_iota.
Qed.

Lemma list_all_ind (Q : Z -> bool) (P : list Z -> Prop):
  P [::] -> 
  (forall i l, Q i -> all Q l -> P l -> P (i::l))->
  (forall l, all Q l -> P l).
Proof.
  move=> hnil hcons; elim => //= a l hrec /andP [hQ hall].
  by apply hcons => //; apply hrec.
Qed.

Lemma ziota_ind (P : list Z -> Prop) p1 p2:
  P [::] -> 
  (forall i l, p1 <= i < p1 + p2 -> P l -> P (i::l))->
  P (ziota p1 p2).
Proof.
  move=> hnil hcons.
  have: all (fun i =>  (p1 <=? i) && (i <? p1 + p2)) (ziota p1 p2).
  + by apply/allP => i; rewrite in_ziota !zify.
  by elim/list_all_ind => // i l; rewrite !zify => *;apply hcons.
Qed.

Lemma all_ziota p1 p2 (f1 f2: Z -> bool) :
  (forall i, (p1 <= i < p1 + p2)%Z -> f1 i = f2 i) ->
  all f1 (ziota p1 p2) = all f2 (ziota p1 p2).
Proof. by move => h; apply ziota_ind => //= i l /h -> ->. Qed.

Lemma ziota_shift i p : ziota i p = map (fun k => i + k)%Z (ziota 0 p).
Proof. by rewrite !ziotaE -map_comp /comp. Qed.

Section ZNTH.
  Context {A: Type} (dfl: A).

  Fixpoint pnth (m: list A) (p: positive) :=
    match m with
    | [::] => dfl
    | a :: m =>
        match p with
        | 1 => a
        | q~1 => pnth m q~0
        | q~0 => pnth m (Pos.pred_double q)
        end%positive
    end.

  Definition znth m (z: Z) : A :=
    if m is a :: m then
      match z with
      | Z0 => a
      | Zpos p => pnth m p
      | Zneg _ => dfl
      end
  else dfl.

End ZNTH.

(* Warning : this is not efficient, it should be used only for proof *)
Definition zindex (T:eqType) (t:T) l :=
  Z.of_nat (seq.index t l).

Lemma znthE (A:Type) dfl (l:list A) i :
  (0 <= i)%Z ->
  znth dfl l i = nth dfl l (Z.to_nat i).
Proof.
  case: l; first by rewrite nth_nil.
  case: i => // p a m _.
  elim/Pos.peano_ind: p a m; first by move => ? [].
  move => p /= ih a; rewrite Pos2Nat.inj_succ /=.
  case; first by rewrite nth_nil.
  move => /= b m.
  by case: Pos.succ (Pos.succ_not_1 p) (Pos.pred_succ p) => // _ _ /= ->.
Qed.

Lemma mem_znth (A:eqType) dfl (l:list A) i :
  [&& 0 <=? i & i <? Z.of_nat (size l)]%Z ->
  znth dfl l i \in l.
Proof.
  move=> /andP []/ZleP h0i /ZltP hi.
  by rewrite znthE //; apply/mem_nth/ZNltP; rewrite Z2Nat.id.
Qed.

Lemma znth_index (T : eqType) (x0 x : T) (s : seq T):
  x \in s → znth x0 s (zindex x s) = x.
Proof.
  move=> hin; rewrite /zindex znthE; last by apply Zle_0_nat.
  by rewrite Nat2Z.id nth_index.
Qed.

(* ------------------------------------------------------------------------- *)
Lemma sumbool_of_boolET (b: bool) (h: b) :
  Sumbool.sumbool_of_bool b = left h.
Proof. by move: h; rewrite /is_true => ?; subst. Qed.

Lemma sumbool_of_boolEF (b: bool) (h: b = false) :
  Sumbool.sumbool_of_bool b = right h.
Proof. by move: h; rewrite /is_true => ?; subst. Qed.


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

(* ------------------------------------------------------------------------- *)
Lemma neq_sym (T: eqType) (x y: T) :
   (x != y) = (y != x).
Proof. apply/eqP; case: eqP => //; exact: not_eq_sym. Qed.

(* ------------------------------------------------------------------------- *)
Lemma nth_not_default T x0 (s:seq T) n x :
  nth x0 s n = x ->
  x0 <> x ->
  (n < size s)%nat.
Proof.
  move=> hnth hneq.
  rewrite ltnNge; apply /negP => hle.
  by rewrite nth_default in hnth.
Qed.

Lemma all_behead {A} {p : A -> bool} {xs : seq A} :
  all p xs -> all p (behead xs).
Proof.
  case: xs => // x xs.
  by move=> /andP [] _.
Qed.

Lemma all2_behead {A B} {p: A -> B -> bool} {xs: seq A} {ys: seq B} :
  all2 p xs ys
  -> all2 p (behead xs) (behead ys).
Proof.
  case: xs; case: ys => //= y ys x xs.
  by move=> /andP [] _.
Qed.

Lemma notin_cons (T : eqType) (x y : T) (s : seq T) :
  (x \notin y :: s) = (x != y) && (x \notin s).
Proof. by rewrite in_cons negb_or. Qed.

(* Convert [ C |- uniq xs -> P ] into
   [ C, ? : x0 <> x1, ? : x0 <> x2, ... |- P ]. *)
Ltac t_elim_uniq :=
  repeat (
    move=> /andP [];
    repeat (rewrite notin_cons; move=> /andP [] /eqP ?);
    move=> _
  );
  move=> _.

Variant and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Variant and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" :=
  (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" :=
  (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" :=
  (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" :=
  (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.

Tactic Notation "have!" ":= " constr(x) :=
  let h := fresh "h" in
  (assert (h := x); move: h).

Tactic Notation "have!" simple_intropattern(ip) ":= " constr(x) :=
  let h := fresh "h" in
  (assert (h := x); move: h => ip).

#[local]
Ltac t_do_rewrites tac :=
  repeat
    match goal with
    | [ h : ?lhs = ?rhs |- _ ] => tac h lhs rhs
    | [ h : is_true (?lhs == ?rhs) |- _ ] => move: h => /eqP h; tac h lhs rhs
    | [ h : is_true ?lhs |- _ ] => tac h lhs true
    end.

#[local]
Ltac head_term e :=
  match e with
  | ?a _ => head_term a
  | _ => e
  end.

#[local]
Ltac is_simpl e :=
  is_var e
  || let x := head_term e in is_constructor x.

#[local]
Ltac simpl_rewrite h lhs rhs :=
  (is_simpl lhs; rewrite -!h) || (is_simpl rhs; rewrite !h).

Ltac t_simpl_rewrites := t_do_rewrites simpl_rewrite.

#[local]
Ltac eq_rewrite h _ _ :=
  (rewrite !h || rewrite -!h); clear h.

Ltac t_eq_rewrites := t_do_rewrites eq_rewrite.

Ltac destruct_opn_args :=
  repeat (t_xrbindP=> -[|?]; first done);
  (t_xrbindP=> -[]; last done).

(* Attempt to prove [injective f] on [eqType]s by case analysis on the
   arguments. *)
Ltac t_inj_cases :=
  move=> [] [] /eqP h;
  apply/eqP.

(* ------------------------------------------------------------------------- *)

Module Option.

Variant option_spec X A o xs xn : option A -> X -> Prop :=
| OptionSpecSome : forall a, o = Some a -> option_spec o xs xn (Some a) (xs a)
| OptionSpecNone : o = None -> option_spec o xs xn None xn.

Lemma oappP R A (f : A -> R) x u : option_spec u f x u (oapp f x u).
Proof. by case: u; constructor. Qed.

Lemma odfltP T (x : T) u : option_spec u id x u (odflt x u).
Proof. by case: u; constructor. Qed.

Lemma obindP A R (f : A -> option R) u : option_spec u f None u (obind f u).
Proof. by case: u; constructor. Qed.

Lemma omapP A R (f : A -> R) u :
  option_spec u (fun x => Some (f x)) None u (Option.map f u).
Proof. by case: u; constructor. Qed.

End Option.

Notation "'let%opt' x ':=' ox 'in' body" :=
  (if ox is Some x then body else None)
  (x strict pattern, at level 25).

Notation "'let%opt '_' ':=' ox 'in' body" :=
  (if ox is Some tt then body else None)
  (at level 25).

Lemma obindP aT bT oa (f : aT -> option bT) a (P : Type) :
  (forall z, oa = Some z -> f z = Some a -> P) ->
  (let%opt a' := oa in f a') = Some a ->
  P.
Proof. case: oa => // a' h h'. exact: (h _ _ h'). Qed.

Definition oassert (b : bool) : option unit :=
  if b then Some tt else None.

Lemma oassertP {A b a} {oa : option A} :
  (let%opt _ := oassert b in oa) = Some a ->
  b /\ oa = Some a.
Proof. by case: b. Qed.

Lemma oassertP_isSome {A b} {oa : option A} :
  isSome (let%opt _ := oassert b in oa) ->
  b /\ isSome oa.
Proof. by case: b. Qed.

Lemma isSomeP {A : Type} {oa : option A} :
  isSome oa ->
  exists a, oa = Some a.
Proof. case: oa; by [|eexists]. Qed.

Lemma o2rP {eT A} {err : eT} {oa : option A} {a} :
  o2r err oa = ok a ->
  oa = Some a.
Proof. by case: oa => //= ? [->]. Qed.

Lemma cat_inj_head T (x y z : seq T) : x ++ y = x ++ z -> y = z.
Proof. by elim: x y z => // > hrec >; rewrite !cat_cons => -[/hrec]. Qed.

Lemma cat_inj_tail T (x y z : seq T) : x ++ z = y ++ z -> x = y.
Proof.
  elim: z x y => >; first by rewrite !cats0.
  by move=> hrec >; rewrite -!cat_rcons => /hrec /rcons_inj[].
Qed.

Lemma map_const_nseq A B (l : list A) (c : B) : map (fun=> c) l = nseq (size l) c.
Proof. by elim: l => // > ? /=; f_equal. Qed.


Section RT_TRANSN.

Context
  {A : Type}
  {R Rstep : A -> A -> Prop}
.

Fixpoint transn_spec_aux (a0 an : A) (l : list A) : Prop :=
  match l with
  | [::] => R a0 an
  | an1 :: l => Rstep an an1 -> transn_spec_aux a0 an1 l
  end.

Definition transn_spec (l : list A) : Prop :=
  match l with
  | [::] => True
  | a0 :: l => transn_spec_aux a0 a0 l
  end.

  Section SPEC.

  Context
    (htrans : forall x y z, R x y -> R y z -> R x z)
    (hstep : forall x y, Rstep x y -> R x y)
    (hrefl : forall x, R x x)
  .

  Lemma transn_spec_auxP a0 an l :
    R a0 an ->
    transn_spec_aux a0 an l.
  Proof.
    elim: l an => //= an1 l hrec an h0n hnn1.
    apply: hrec.
    apply: (htrans h0n).
    exact: hstep.
  Qed.

  Lemma transn_specP l : transn_spec l.
  Proof.
    case: l => [// | a0 [// | a1 l ?]].
    apply: transn_spec_auxP.
    exact: hstep.
  Qed.

  End SPEC.

Context (hspec : forall l, transn_spec l).

Lemma transn2 a0 a1 a2 :
  Rstep a0 a1 ->
  Rstep a1 a2 ->
  R a0 a2.
Proof. exact: (hspec [:: _; _; _ ]). Qed.

Lemma transn3 a0 a1 a2 a3 :
  Rstep a0 a1 ->
  Rstep a1 a2 ->
  Rstep a2 a3 ->
  R a0 a3.
Proof. exact: (hspec [:: _; _; _; _ ]). Qed.

Lemma transn4 a0 a1 a3 a2 a4 :
  Rstep a0 a1 ->
  Rstep a1 a2 ->
  Rstep a2 a3 ->
  Rstep a3 a4 ->
  R a0 a4.
Proof. exact: (hspec [:: _; _; _; _; _ ]). Qed.

Lemma transn5 a0 a1 a3 a2 a4 a5 :
  Rstep a0 a1 ->
  Rstep a1 a2 ->
  Rstep a2 a3 ->
  Rstep a3 a4 ->
  Rstep a4 a5 ->
  R a0 a5.
Proof. exact: (hspec [:: _; _; _; _; _; _ ]). Qed.

Lemma transn6 a0 a1 a3 a2 a4 a5 a6 :
  Rstep a0 a1 ->
  Rstep a1 a2 ->
  Rstep a2 a3 ->
  Rstep a3 a4 ->
  Rstep a4 a5 ->
  Rstep a5 a6 ->
  R a0 a6.
Proof. exact: (hspec [:: _; _; _; _; _; _; _ ]). Qed.

End RT_TRANSN.
