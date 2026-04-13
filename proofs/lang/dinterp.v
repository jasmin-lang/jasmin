(* Two probabilistic interpretations of ITrees.
   One uses the distribution monad and [iter] (can't use [interp] because of
   universe clashes).
   The other directly constructs a distribution from the ITree. *)

From Coq Require Import Classical.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssralg ssrnum.
From mathcomp Require Import
  bigop
  boolp
  choice
  constructive_ereal
  distr
  eqtype
  fintype
  matrix
  order
  reals
.
From ExtLib Require Structures.Functor Structures.Monad.
From ITree Require Basics.Basics.
From ITree Require ITree ITreeFacts Interp.Interp.

Import GRing.Theory Num.Theory Order Order.Theory.

Require Import distr_extra eqit_facts.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------------- *)
(* Random sampling *)

Section RND.

Import ITree.

Context {R : realType}.

Variant Rnd : Type -> Type :=
| GetRnd : forall {A : finType}, distr R A -> Rnd A.

Definition unif_rV {T : finType} (n : nat) : itree Rnd 'rV[T]_n :=
  trigger (GetRnd (dunif 'rV[T]_n)).

End RND.

(* -------------------------------------------------------------------------- *)
(* Distribution monad using ITrees *)

Section ITREE.

Context {R : realType}.

Section DistrMonad.

Import Structures.Functor Structures.Monad Basics.Basics.

Set Universe Polymorphism.

Definition DistrM (A : Type) : Type := {distr {classic A} / R}.

Let distr_fmap A B (f : A -> B) (d : DistrM A) :=
  dmargin (T := {classic A}) (U := {classic B}) f d.

#[global]
Instance Functor_DistrM : Functor DistrM := { fmap := distr_fmap; }.

Definition distrD A (mu : distr R A) :=
  dmargin (T := A) (U := {classic A}) id mu.
Let dunitD A a : DistrM A := dunit (T := {classic A}) a.
Let dbindD A B mu f := dlet (R := R) (T := {classic A}) (U := {classic B}) f mu.

Notation "\dletD_ ( i <- d ) E" := (dbindD d (fun i => E))
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dletD_ ( i  <-  d ) '/  '  E ']'").

#[global]
Instance Monad_DistrM : Monad DistrM := { ret := dunitD; bind := dbindD; }.

Fixpoint iter_n I A (step : I -> DistrM (I + A)) (i : I) (n : nat) : DistrM A :=
  match n with
  | 0 => dnull (T := {classic A})
  | S n' =>
    \dletD_(lr <- step i)
      match lr with
      | inl i' => iter_n step i' n'
      | inr a  => dunitD a
      end
  end.

#[global]
Instance MonadIter_DistrM : MonadIter DistrM :=
  fun A I step i => \dlim_(n) iter_n step i n.

End DistrMonad.

(* -------------------------------------------------------------------------- *)
(* Interpretation of Rnd events as distributions *)

Section DINTERP.

Import ITree Structures.Functor Structures.Monad Basics.Basics.

Definition handle_Rnd : forall T, Rnd (R := R) T -> DistrM T :=
  fun _ e => let 'GetRnd _ mu := e in distrD mu.

End DINTERP.

End ITREE.

Import ITree.ITree Structures.Functor Structures.Monad Basics.Basics.

(* The bypass is apparently needed and rules out many lemmas from ITrees and
   mathcomp. *)
#[bypass_check(universes)]
Definition dinterp_itree
{R : realType} {T} (t : itree (Rnd (R := R)) T) : DistrM (R := R) T :=
  iter (M := DistrM (R := R))
    (fun t0 =>
      match observe t0 with
      | RetF r => ret (m := DistrM (R := R)) (inr r)
      | TauF t => ret (m := DistrM (R := R)) (inl t)
      | VisF _ e k =>
          fmap (F := DistrM (R := R))
            (fun x => inl (k x)) (handle_Rnd (R := R) e)
      end) t.

(* -------------------------------------------------------------------------- *)
(* Direct interpretation of itrees as distributions *)

Section DIRECT.

Import ITree ITreeFacts.

Context {R : realType}.

Section INTERP.

  Context {T : choiceType}.

  Fixpoint dinterp' (t : itree' Rnd T) (n : nat) : distr R T :=
    if n is n.+1 then
      match t with
      | RetF r => dunit r
      | TauF t => dinterp' (observe t) n
      | VisF _ e k =>
          match e in Rnd A return (A -> itree Rnd T) -> distr R T with
          | GetRnd _ mu =>
              fun k0 => \dlet_(t <- mu) (dinterp' (observe (k0 t)) n)
          end k
      end
    else dnull.

  Definition dinterp (t : itree Rnd T) : distr R T :=
    dlim (dinterp' (observe t)).

  Lemma dinterp'_step t n : dle (dinterp' t n) (dinterp' t n.+1).
  Proof.
  elim: n t => [|n hind] t s; first exact: lef_dnull.
  case: t => [//| t | A e k]; first exact: hind.
  case: e k => A' mu k. apply: le_in_dlet => /= bs hbs s'. exact: hind.
  Qed.

  Lemma dinterp'_mono t n m :
    (n <= m)%nat ->
    dle (dinterp' t n) (dinterp' t m).
  Proof.
  move=> h; rewrite -(addnK n m) subDnCA //. elim: (m - n)%nat => [|d hind].
  - by rewrite addn0.
  rewrite addnS => s; exact: Order.le_trans (hind _) (dinterp'_step _ _ _).
  Qed.

End INTERP.

Section ONE.

Context {T T' : choiceType} (RR : T -> T' -> Prop).

Notation eqit_ind := (eqit_ind (E := Rnd (R := R)) (R := T) (R' := T')).

Lemma one_way (t : itree Rnd T) (t' : itree Rnd T') :
  eutt RR t t' ->
  forall n, exists m,
    dleX RR (dinterp' (observe t) n) (dinterp' (observe t') m).
Proof.
move=> h n; elim: n t t' h => [|n hind] t t' h.
- exists 0 => X Y _; by rewrite pr_dnull ge0_pr.
elim/eqit_ind: h =>
  {t t'} [ _ _ r1 r2 -> -> h
         | _ _ t t' -> -> h
         | _ _ _ [A mu] k k' -> -> h
         | _ ot t -> _ h [m hm]
         | _ t ot -> _ h [m hm] ].
- exists 1 => X Y /(_ r1 r2 h) hXY; rewrite /= !pr_dunit.
  by case hx: (X _) hXY => // /(_ erefl) ->.
- move: h => /hind [m hle]; by exists m.+1.
- have:
    forall v,
      exists m,
        dleX RR (dinterp' (observe (k v)) n) (dinterp' (observe (k' v)) m).
  + move=> v; apply: hind; exact: h.
  move=> /ClassicalChoice.choice [get {}h].
  exists (\max_i get i).+1 => X Y hXY /=.
  apply: (Order.le_trans (pr_dlet _ h hXY)). apply: le_mu_pr => r2 hX hX'.
  apply: le_in_dlet => /= t ht r2' {r2 hX hX'}. apply: dinterp'_mono.
  exact: leq_bigmax.
- apply/hind/eqitE; exact: h.
exists m.+1; exact: hm.
Qed.

End ONE.

Lemma eutt_deqX {T T' : choiceType} RR (t : itree Rnd T) (t' : itree Rnd T') :
  eutt RR t t' ->
  deqX RR (dinterp t) (dinterp t').
Proof.
have hmonot := dinterp'_mono (observe t).
have hmonot' := dinterp'_mono (observe t').
move=> h; apply: dle_anti.
+ by apply (leX_dlim hmonot hmonot'), one_way.
apply (leX_dlim hmonot' hmonot), one_way; exact: eutt_flip h.
Qed.

Theorem dinterp_eutt {T : choiceType} (t t' : itree Rnd T) :
  eutt eq t t' ->
  dinterp t =1 dinterp t'.
Proof. move=> h; exact/deqX_eq/eutt_deqX. Qed.

End DIRECT.
