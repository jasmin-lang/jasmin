(* Two probabilistic interpretations of ITrees.
   It constructs a distribution from the ITree. *)

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
