(* * Utility definition for dmasm *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrnat ssrbool seq choice finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

(* ** LEM
 * -------------------------------------------------------------------- *)

Axiom LEM : forall {T : Type}, forall (x y : T), {x=y}+{x<>y}.

(* ** Admit
 * -------------------------------------------------------------------- *)

Definition admit {T: Type} : T.  Admitted.

(* ** Option monad
 * -------------------------------------------------------------------- *)

Notation "m >>= f" := (obind f m) (at level 25, left associativity).

Fixpoint mapM aT bT (f : aT -> option bT) (xs : seq aT) : option (seq bT) :=
  match xs with
  | [::] =>
      Some [::]
  | [:: x & xs] =>
      f x >>= fun y =>
      mapM f xs >>= fun ys =>
      Some [:: y & ys]
  end.

Fixpoint foldM aT bT (f : aT -> bT -> option bT) (acc : bT) (l : seq aT) :=
  match l with
  | [::]         => Some acc
  | [:: a & la ] => f a acc >>= fun acc => foldM f acc la
  end.

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

Fixpoint unions_seq (K : choiceType) (ss : seq {fset K}) : {fset K} :=
  match ss with
  | [::]         => fset0
  | [:: x & xs ] => x `|` unions_seq xs
  end.

Definition unions (K : choiceType) (ss : {fset {fset K}}) : {fset K} :=
  unions_seq (fset_keys ss).


Definition oeq aT (f : aT -> aT -> Prop) (o1 o2 : option aT) :=
  match o1, o2 with
  | Some x1, Some x2 => f x1 x2
  | None,    None    => true
  | _ ,      _       => false
  end.

(*
Lemma SomeEqK aT (a b : aT):
  Some a = Some b -> a = b.
Proof. move=> []. done. Qed.
*)

(* ** Fmap equality on subset of keys
 * -------------------------------------------------------------------- *)

Definition eq_on (K : choiceType) V (s : {fset K}) (m1 m2 : {fmap K -> V}) :=
  m1.[& s] = m2.[& s].

Notation "m1 = m2 [& s ]" := (eq_on s m1 m2) (at level 70, m2 at next level,
  format "'[hv ' m1  '/' =  m2  '/' [&  s ] ']'").

Section EqOn.

Variable K : choiceType.
Variable V : Type.

Lemma eq_on_fsubset (s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  s1 `<=` s2 ->
  m1 = m2 [& s2] ->
  m1 = m2 [& s1].
Proof.
rewrite /eq_on; move=> Hsub Hs2.
move: (f_equal (fun m => m.[& s1]) Hs2); rewrite !restrictf_comp.
by rewrite (_ : s2 `&` s1 = s1); [ | exact (fsetIidPr Hsub) ].
Qed.

Lemma eq_on_Ur(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|` s2] ->
  m1 = m2 [& s2].
Proof. by apply eq_on_fsubset; apply /fsetUidPr; rewrite fsetUCA fsetUid /=. Qed.

Lemma eq_on_Ul(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|`  s2]->
  m1 = m2 [& s1].
Proof. by apply eq_on_fsubset; apply /fsetUidPr; rewrite fsetUA fsetUid /=. Qed.

Lemma eq_on_U(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|`  s2] ->
  m1 = m2 [& s1] /\ m1 = m2 [& s2].
Proof. by move=> HU; split; [ apply: eq_on_Ul HU | apply: eq_on_Ur HU ]. Qed.

Lemma eq_on_get_in (s : {fset K}) (m1 m2 : {fmap K -> V}) (k : K) :
  m1 = m2 [& s] ->
  k \in s ->
  m1.[? k] = m2.[? k].
Proof.
move=> Heq_on Hin.
rewrite (_: m1.[? k] = m1.[& s].[? k]). 
+ by rewrite Heq_on fnd_restrict Hin.
by rewrite fnd_restrict Hin.
Qed.

Lemma eq_on_get_fset1 (m1 m2 : {fmap K -> V}) (k : K) :
  m1 = m2 [& [fset k]] ->
  m1.[? k] = m2.[? k].
Proof. by move=> Heq_on; apply: (eq_on_get_in Heq_on); rewrite in_fset1. Qed.

Lemma eq_on_setf_same (s : {fset K}) (m1 m2 : {fmap K -> V}) k v:
  m1 = m2 [& s] ->
  m1.[k <- v] = m2.[k <- v] [& s].
Proof.
rewrite /eq_on !restrictf_set /= => Heq.
case (k \in s); last done.
admit.
Qed.

End EqOn.

Definition oeq_on (K : choiceType) V (s : {fset K}) (m1 m2 : option {fmap K -> V}) :=
  oeq (eq_on s) m1 m2.

Notation "m1 = m2 [&& s ]" := (oeq_on s m1 m2) (at level 70, m2 at next level,
  format "'[hv ' m1  '/' =  m2  '/' [&&  s ] ']'").

