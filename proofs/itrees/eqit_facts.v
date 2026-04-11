From Coq Require Import Classical.
From mathcomp Require Import ssreflect ssrbool ssrfun.

From ITree Require Import ITree ITreeFacts.
From Paco Require Import paco.

Section ITREE.

Context
  {E : Type -> Type}
  {R R' : Type}
  (RR : R -> R' -> Prop)
  (weakL weakR : bool)
.

Notation eqit := (eqit RR weakL weakR) (only parsing).
Notation eqitF := (eqitF RR weakL weakR id eqit) (only parsing).

Lemma eqitE (t : itree E R) (t' : itree E R') :
  eqit t t' <-> eqitF (observe t) (observe t').
Proof.
split.
- move=> h. punfold h. red in h. apply: eqitF_mono;
    [exact: h | exact: eqit_idclo_mono | done | by move=> ?? -[]].
move=> h. pstep. red. apply: eqitF_mono;
  [exact: h | exact: eqit_idclo_mono | done | by left ].
Qed.

Context
  (P : itree E R -> itree E R' -> Prop)
  (hret :
    forall t t' r r',
      observe t = RetF r ->
      observe t' = RetF r' ->
      RR r r' ->
      P t t')
  (htau :
    forall t t' ot ot',
      observe t = TauF ot ->
      observe t' = TauF ot' ->
      eqit ot ot' ->
      P t t')
  (hvis :
    forall t t' A e k k',
      observe t = VisF e k ->
      observe t' = VisF e k' ->
      (forall v : A, eqit (k v) (k' v)) ->
      P t t')
  (htaul :
    forall t ot t',
      observe t = TauF ot ->
      weakL ->
      eqitF (observe ot) (observe t') ->
      P ot t' ->
      P t t')
  (htaur :
    forall t' t ot',
      observe t' = TauF ot' ->
      weakR ->
      eqitF (observe t) (observe ot') ->
      P t ot' ->
      P t t').

Lemma eqit_ind t t' : eqit t t' -> P t t'.
Proof.
move=> h.
punfold h; red in h.
elim: h {-2}t {-2}t' (erefl (observe t)) (erefl (observe t')) => {t t'}
  [ r1 r2 h t t' ht ht'
  | ot ot' [h|//] t t' ht ht'
  | A e k k' h t t' ht ht'
  | t0 ot hweakL h hind t t' ht ht'
  | t0 ot hweakR h hind t t' ht ht' ].
- exact: hret ht ht' h.
- exact: htau ht ht' h.
- apply: (hvis ht ht') => v; by case: (h v).
- apply: (htaul ht hweakL); last exact: hind.
  apply/eqitE. pstep. red. by rewrite ht'.
apply: (htaur  ht' hweakR); last exact: hind.
apply/eqitE. pstep. red. by rewrite ht.
Qed.

End ITREE.
